import hologram_ffi as hg
import json

# Create executor
exec_handle = hg.new_executor()

# Allocate buffers
size = 1000
a_handle = hg.executor_allocate_buffer(exec_handle, size)
b_handle = hg.executor_allocate_buffer(exec_handle, size)
c_handle = hg.executor_allocate_buffer(exec_handle, size)

# Prepare data
data_a = [float(i) for i in range(size)]
data_b = [float(i * 2) for i in range(size)]

# Copy to buffers
hg.buffer_copy_from_slice(exec_handle, a_handle, json.dumps(data_a))
hg.buffer_copy_from_slice(exec_handle, b_handle, json.dumps(data_b))

# Execute vector addition
hg.vector_add_f32(exec_handle, a_handle, b_handle, c_handle, size)

# Read results
result_json = hg.buffer_to_vec(exec_handle, c_handle)
result = json.loads(result_json)

print(f"Result: {result[:10]}")  # First 10 elements

# Cleanup
hg.buffer_cleanup(a_handle)
hg.buffer_cleanup(b_handle)
hg.buffer_cleanup(c_handle)
hg.executor_cleanup(exec_handle)
