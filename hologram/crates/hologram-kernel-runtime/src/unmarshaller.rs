/// Unmarshals binary parameters into typed values
///
/// This provides a consistent way to unpack parameters that were
/// marshalled using little-endian byte order.
pub struct Unmarshaller<'a> {
    buffer: &'a [u8],
    offset: usize,
}

impl<'a> Unmarshaller<'a> {
    pub fn new(buffer: &'a [u8]) -> Self {
        Self { buffer, offset: 0 }
    }

    /// Align offset to specified alignment boundary
    fn align(&mut self, alignment: usize) {
        let misalignment = self.offset % alignment;
        if misalignment != 0 {
            self.offset += alignment - misalignment;
        }
    }

    // ===== Integer Types =====

    pub fn unpack_u8(&mut self) -> u8 {
        self.align(1);
        let byte = self.buffer[self.offset];
        self.offset += 1;
        byte
    }

    pub fn unpack_u16(&mut self) -> u16 {
        self.align(2);
        let bytes = &self.buffer[self.offset..self.offset + 2];
        self.offset += 2;
        u16::from_le_bytes([bytes[0], bytes[1]])
    }

    pub fn unpack_u32(&mut self) -> u32 {
        self.align(4);
        let bytes = &self.buffer[self.offset..self.offset + 4];
        self.offset += 4;
        u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
    }

    pub fn unpack_u64(&mut self) -> u64 {
        self.align(8);
        let bytes = &self.buffer[self.offset..self.offset + 8];
        self.offset += 8;
        u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ])
    }

    pub fn unpack_i8(&mut self) -> i8 {
        self.unpack_u8() as i8
    }

    pub fn unpack_i16(&mut self) -> i16 {
        self.unpack_u16() as i16
    }

    pub fn unpack_i32(&mut self) -> i32 {
        self.unpack_u32() as i32
    }

    pub fn unpack_i64(&mut self) -> i64 {
        self.unpack_u64() as i64
    }

    // ===== Floating Point Types =====

    pub fn unpack_f32(&mut self) -> f32 {
        self.align(4);
        let bytes = &self.buffer[self.offset..self.offset + 4];
        self.offset += 4;
        f32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
    }

    pub fn unpack_f64(&mut self) -> f64 {
        self.align(8);
        let bytes = &self.buffer[self.offset..self.offset + 8];
        self.offset += 8;
        f64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ])
    }

    // ===== Pointer Types =====

    pub fn unpack_device_ptr(&mut self) -> u64 {
        self.unpack_u64()
    }

    /// Unpack device array pointer and return as a typed pointer
    pub fn unpack_ptr<T>(&mut self) -> *const T {
        self.unpack_device_ptr() as *const T
    }

    /// Unpack device array pointer and return as a typed mutable pointer
    pub fn unpack_mut_ptr<T>(&mut self) -> *mut T {
        self.unpack_device_ptr() as *mut T
    }

    // ===== Result-returning versions (for error handling) =====

    pub fn try_unpack_f32(&mut self) -> Result<f32, String> {
        if self.offset + 4 > self.buffer.len() {
            return Err("buffer too small for f32".to_string());
        }
        Ok(self.unpack_f32())
    }

    pub fn try_unpack_u32(&mut self) -> Result<u32, String> {
        if self.offset + 4 > self.buffer.len() {
            return Err("buffer too small for u32".to_string());
        }
        Ok(self.unpack_u32())
    }

    pub fn try_unpack_i32(&mut self) -> Result<i32, String> {
        if self.offset + 4 > self.buffer.len() {
            return Err("buffer too small for i32".to_string());
        }
        Ok(self.unpack_i32())
    }

    pub fn try_unpack_i64(&mut self) -> Result<i64, String> {
        if self.offset + 8 > self.buffer.len() {
            return Err("buffer too small for i64".to_string());
        }
        Ok(self.unpack_i64())
    }

    pub fn try_unpack_u8(&mut self) -> Result<u8, String> {
        if self.offset + 1 > self.buffer.len() {
            return Err("buffer too small for u8".to_string());
        }
        Ok(self.unpack_u8())
    }

    pub fn try_unpack_u16(&mut self) -> Result<u16, String> {
        if self.offset + 2 > self.buffer.len() {
            return Err("buffer too small for u16".to_string());
        }
        Ok(self.unpack_u16())
    }

    pub fn try_unpack_u64(&mut self) -> Result<u64, String> {
        if self.offset + 8 > self.buffer.len() {
            return Err("buffer too small for u64".to_string());
        }
        Ok(self.unpack_u64())
    }

    pub fn try_unpack_device_ptr(&mut self) -> Result<u64, String> {
        self.try_unpack_u64()
    }

    pub fn try_unpack_f64(&mut self) -> Result<f64, String> {
        if self.offset + 8 > self.buffer.len() {
            return Err("buffer too small for f64".to_string());
        }
        Ok(self.unpack_f64())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unpack_primitives() {
        let mut buf = Vec::new();
        // Align to 2 bytes for u16
        let u16_val: u16 = 1;
        buf.extend_from_slice(&u16_val.to_le_bytes());

        // Align to 4 bytes for u32
        while buf.len() % 4 != 0 {
            buf.push(0);
        }
        let u32_val: u32 = 2;
        buf.extend_from_slice(&u32_val.to_le_bytes());

        // Align to 8 bytes for u64
        while buf.len() % 8 != 0 {
            buf.push(0);
        }
        let u64_val: u64 = 3;
        buf.extend_from_slice(&u64_val.to_le_bytes());

        // Align to 4 bytes for f32
        while buf.len() % 4 != 0 {
            buf.push(0);
        }
        let f32_val: f32 = 4.0;
        buf.extend_from_slice(&f32_val.to_le_bytes());

        // Align to 8 bytes for f64
        while buf.len() % 8 != 0 {
            buf.push(0);
        }
        let f64_val: f64 = 5.0;
        buf.extend_from_slice(&f64_val.to_le_bytes());

        let mut u = Unmarshaller::new(&buf);
        assert_eq!(u.unpack_u16(), 1);
        assert_eq!(u.unpack_u32(), 2);
        assert_eq!(u.unpack_u64(), 3);
        assert_eq!(u.unpack_f32(), 4.0);
        assert_eq!(u.unpack_f64(), 5.0);
    }
}
