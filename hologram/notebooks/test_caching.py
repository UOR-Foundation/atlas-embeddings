#!/usr/bin/env python3
"""Test if StaticEngine caching is working"""

import numpy as np
import time
import sys
sys.path.insert(0, '/workspaces/hologramapp/crates/hologram-py/target/wheels')
import hologram as hg

print("Testing StaticEngine Caching Behavior")
print("=" * 60)

# Create executor
exec = hg.Executor()

# Create test data
size = 10000
a = exec.from_numpy(np.ones(size, dtype=np.float32))
b = exec.from_numpy(np.ones(size, dtype=np.float32))

print(f"\nTesting vector_add with size={size}")
print("-" * 60)

# First call (cold - might compile)
start = time.perf_counter()
result1 = hg.ops.vector_add(a, b)
time1 = (time.perf_counter() - start) * 1000
print(f"Call 1 (cold):  {time1:.3f} ms")

# Second call (should be cached)
start = time.perf_counter()
result2 = hg.ops.vector_add(a, b)
time2 = (time.perf_counter() - start) * 1000
print(f"Call 2 (warm):  {time2:.3f} ms")

# Third call (should be cached)
start = time.perf_counter()
result3 = hg.ops.vector_add(a, b)
time3 = (time.perf_counter() - start) * 1000
print(f"Call 3 (warm):  {time3:.3f} ms")

# Fourth call (should be cached)
start = time.perf_counter()
result4 = hg.ops.vector_add(a, b)
time4 = (time.perf_counter() - start) * 1000
print(f"Call 4 (warm):  {time4:.3f} ms")

# Fifth call (should be cached)
start = time.perf_counter()
result5 = hg.ops.vector_add(a, b)
time5 = (time.perf_counter() - start) * 1000
print(f"Call 5 (warm):  {time5:.3f} ms")

print("\n" + "=" * 60)
print("Analysis:")
print("-" * 60)

if time1 > time2 * 2:
    print(f"✅ First call is {time1/time2:.1f}x slower - caching appears to be working!")
    print(f"   Compilation overhead: ~{time1 - time2:.3f} ms")
    print(f"   Cached execution time: ~{time2:.3f} ms")
else:
    print(f"⚠️  First call ({time1:.3f}ms) not significantly slower than second ({time2:.3f}ms)")
    print(f"   Either: (a) caching already worked, (b) no caching, or (c) cache overhead is small")

avg_warm = (time2 + time3 + time4 + time5) / 4
print(f"\nAverage warm execution time: {avg_warm:.3f} ms")
print(f"This is the interpreter execution overhead (not compilation)")
