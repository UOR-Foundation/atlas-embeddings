//! Metal compute pipeline management and shader compilation
//!
//! Manages Metal compute pipelines with caching for optimal performance.

#[cfg(target_vendor = "apple")]
use metal::{ComputePipelineState, Device, Library};

/// Metal shader source embedded at compile time
#[cfg(target_vendor = "apple")]
const METAL_SHADER_SOURCE: &str = include_str!("shaders.metal");

/// Metal pipeline cache for compiled compute kernels
#[cfg(target_vendor = "apple")]
pub struct PipelineCache {
    /// Metal device
    device: Device,

    /// Compiled shader library
    library: Library,

    /// Cached compute pipeline states (kernel_name -> pipeline)
    pipelines: HashMap<String, ComputePipelineState>,
}

#[cfg(target_vendor = "apple")]
impl PipelineCache {
    /// Create a new pipeline cache and compile shaders
    ///
    /// # Errors
    ///
    /// Returns an error if shader compilation fails
    pub fn new(device: Device) -> Result<Self> {
        // Compile Metal shader library
        let library = device
            .new_library_with_source(METAL_SHADER_SOURCE, &metal::CompileOptions::new())
            .map_err(|e| BackendError::Other(format!("Failed to compile Metal shaders: {}", e)))?;

        Ok(Self {
            device,
            library,
            pipelines: HashMap::new(),
        })
    }

    /// Get or create a compute pipeline for the given kernel
    ///
    /// Pipelines are cached after first creation for performance.
    ///
    /// # Arguments
    ///
    /// * `kernel_name` - Name of the kernel function (e.g., "atlas_add_f32")
    ///
    /// # Returns
    ///
    /// Compute pipeline state for the kernel
    ///
    /// # Errors
    ///
    /// Returns an error if the kernel is not found or pipeline creation fails
    pub fn get_pipeline(&mut self, kernel_name: &str) -> Result<&ComputePipelineState> {
        // Check cache first
        if !self.pipelines.contains_key(kernel_name) {
            // Get kernel function from library
            let function = self.library.get_function(kernel_name, None).map_err(|e| {
                BackendError::Other(format!("Kernel '{}' not found in shader library: {}", kernel_name, e))
            })?;

            // Create compute pipeline
            let pipeline = self
                .device
                .new_compute_pipeline_state_with_function(&function)
                .map_err(|e| BackendError::Other(format!("Failed to create pipeline for '{}': {}", kernel_name, e)))?;

            // Cache pipeline
            self.pipelines.insert(kernel_name.to_string(), pipeline);
        }

        Ok(self.pipelines.get(kernel_name).unwrap())
    }

    /// Get all available kernel names
    pub fn kernel_names(&self) -> Vec<String> {
        self.library
            .function_names()
            .iter()
            .map(|name| name.to_string())
            .collect()
    }

    /// Get number of cached pipelines
    pub fn cached_pipeline_count(&self) -> usize {
        self.pipelines.len()
    }

    /// Clear pipeline cache
    pub fn clear_cache(&mut self) {
        self.pipelines.clear();
    }
}

#[cfg(test)]
#[cfg(target_vendor = "apple")]
mod tests {
    use super::*;
    use metal::Device;

    #[test]
    fn test_pipeline_cache_creation() {
        let device = Device::system_default().unwrap();
        let cache = PipelineCache::new(device).unwrap();

        // Should have compiled shader library
        assert!(cache.kernel_names().len() > 0);
    }

    #[test]
    fn test_get_pipeline() {
        let device = Device::system_default().unwrap();
        let mut cache = PipelineCache::new(device).unwrap();

        // Get pipeline for vector add
        let pipeline = cache.get_pipeline("atlas_add_f32").unwrap();
        assert_eq!(cache.cached_pipeline_count(), 1);

        // Getting again should use cache
        let pipeline2 = cache.get_pipeline("atlas_add_f32").unwrap();
        assert_eq!(cache.cached_pipeline_count(), 1);

        // Pipelines should be the same reference
        assert!(std::ptr::eq(pipeline, pipeline2));
    }

    #[test]
    fn test_all_kernels_compile() {
        let device = Device::system_default().unwrap();
        let mut cache = PipelineCache::new(device).unwrap();

        // Try to get all kernels
        let kernel_names = cache.kernel_names();
        assert!(kernel_names.len() > 20, "Expected at least 20 kernels");

        for kernel_name in kernel_names {
            cache.get_pipeline(&kernel_name).unwrap();
        }

        // All kernels should be cached now
        assert!(cache.cached_pipeline_count() > 20);
    }

    #[test]
    fn test_clear_cache() {
        let device = Device::system_default().unwrap();
        let mut cache = PipelineCache::new(device).unwrap();

        cache.get_pipeline("atlas_add_f32").unwrap();
        assert_eq!(cache.cached_pipeline_count(), 1);

        cache.clear_cache();
        assert_eq!(cache.cached_pipeline_count(), 0);

        // Should be able to get pipeline again after clear
        cache.get_pipeline("atlas_add_f32").unwrap();
        assert_eq!(cache.cached_pipeline_count(), 1);
    }

    #[test]
    fn test_nonexistent_kernel() {
        let device = Device::system_default().unwrap();
        let mut cache = PipelineCache::new(device).unwrap();

        // Try to get non-existent kernel
        let result = cache.get_pipeline("atlas_nonexistent_kernel");
        assert!(result.is_err());
    }
}
