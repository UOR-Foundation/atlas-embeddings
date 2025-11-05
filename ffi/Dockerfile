# Docker container for UOR FFI builds with Lean runtime
# This provides a consistent environment with matching C++ toolchain
# Solves the libc++ vs libstdc++ incompatibility issue

FROM ubuntu:24.04

# Prevent interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Install base dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    make \
    gcc \
    g++ \
    clang-18 \
    libc++-18-dev \
    libc++abi-18-dev \
    libgmp-dev \
    libuv1-dev \
    time \
    clang-format-18 \
    doxygen \
    graphviz \
    valgrind \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

# Set up clang-18 as default
RUN update-alternatives --install /usr/bin/clang clang /usr/bin/clang-18 100 && \
    update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-18 100 && \
    update-alternatives --install /usr/bin/clang-format clang-format /usr/bin/clang-format-18 100

# Install Lean toolchain
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# Set up consistent C++ toolchain
ENV CC=clang
ENV CXX=clang++
ENV CXXFLAGS="-stdlib=libc++"
ENV LDFLAGS="-stdlib=libc++ -lc++abi"

# Create working directory
WORKDIR /workspace

# Copy the project files
COPY . .

# Build Lean modules
RUN lake build UOR || true

# Build FFI components with both pure C and Lean runtime
RUN cd ffi && \
    make clean && \
    make test-pure && \
    make build && \
    make test && \
    make verify && \
    make pkg-config && \
    cd examples && make all

# Run all tests and benchmarks
RUN cd ffi && \
    examples/simple && \
    examples/advanced && \
    make benchmark

# Default command
CMD ["make", "-C", "ffi", "help"]