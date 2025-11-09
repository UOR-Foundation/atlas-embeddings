cmake_minimum_required(VERSION 3.12)
project(AtlasBridge VERSION 0.5.0 LANGUAGES C)

# Options
option(USE_BLAS "Enable BLAS acceleration for matrix-vector operations" ON)
option(USE_AVX2 "Enable AVX2 SIMD acceleration (x86_64 only)" ON)
option(BUILD_SHARED_LIBS "Build shared library" ON)
option(BUILD_STATIC_LIBS "Build static library" OFF)
option(BUILD_TESTS "Build test executables" ON)

# C standard
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)

# Compiler flags
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra")
set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -O2")
set(CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} -g -O0")

# Atlas core library source
set(ATLAS_CORE_SOURCES
    atlas_core/src/atlas_bridge_ctx.c
)

set(ATLAS_CORE_HEADERS
    atlas_core/include/atlas_bridge_ctx.h
)

# BLAS detection
if(USE_BLAS)
    message(STATUS "BLAS acceleration: ENABLED (searching...)")
    
    # Try to find BLAS using CMake's built-in module
    find_package(BLAS QUIET)
    
    if(BLAS_FOUND)
        message(STATUS "Found BLAS: ${BLAS_LIBRARIES}")
        add_compile_definitions(USE_BLAS)
        set(BLAS_LINK_LIBS ${BLAS_LIBRARIES})
    else()
        # Try pkg-config for OpenBLAS
        find_package(PkgConfig QUIET)
        if(PKG_CONFIG_FOUND)
            pkg_check_modules(OPENBLAS QUIET openblas)
            if(OPENBLAS_FOUND)
                message(STATUS "Found OpenBLAS via pkg-config")
                add_compile_definitions(USE_BLAS)
                include_directories(${OPENBLAS_INCLUDE_DIRS})
                set(BLAS_LINK_LIBS ${OPENBLAS_LIBRARIES})
            else()
                message(WARNING "BLAS not found, using fallback naive loops")
            endif()
        else()
            message(WARNING "BLAS not found, using fallback naive loops")
        endif()
    endif()
else()
    message(STATUS "BLAS acceleration: DISABLED")
endif()

# AVX2 detection and flags
if(USE_AVX2)
    message(STATUS "AVX2 SIMD acceleration: ENABLED")
    include(CheckCCompilerFlag)
    check_c_compiler_flag("-mavx2" COMPILER_SUPPORTS_AVX2)
    
    if(COMPILER_SUPPORTS_AVX2)
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -mavx2")
        message(STATUS "Compiler supports AVX2")
    else()
        message(WARNING "Compiler does not support AVX2, using scalar fallback")
    endif()
else()
    message(STATUS "AVX2 SIMD acceleration: DISABLED")
endif()

# Include directories
include_directories(atlas_core/include)

# Shared library
if(BUILD_SHARED_LIBS)
    add_library(atlas_bridge_ctx SHARED ${ATLAS_CORE_SOURCES})
    target_link_libraries(atlas_bridge_ctx m ${BLAS_LINK_LIBS})
    set_target_properties(atlas_bridge_ctx PROPERTIES
        VERSION ${PROJECT_VERSION}
        SOVERSION ${PROJECT_VERSION_MAJOR}
        PUBLIC_HEADER "${ATLAS_CORE_HEADERS}"
    )
    
    install(TARGETS atlas_bridge_ctx
        LIBRARY DESTINATION lib
        PUBLIC_HEADER DESTINATION include/atlas_bridge
    )
endif()

# Static library
if(BUILD_STATIC_LIBS)
    add_library(atlas_bridge_ctx_static STATIC ${ATLAS_CORE_SOURCES})
    target_link_libraries(atlas_bridge_ctx_static m ${BLAS_LINK_LIBS})
    set_target_properties(atlas_bridge_ctx_static PROPERTIES
        OUTPUT_NAME atlas_bridge_ctx
        PUBLIC_HEADER "${ATLAS_CORE_HEADERS}"
    )
    
    install(TARGETS atlas_bridge_ctx_static
        ARCHIVE DESTINATION lib
        PUBLIC_HEADER DESTINATION include/atlas_bridge
    )
endif()

# Test executables
if(BUILD_TESTS)
    # Test dependencies
    set(TEST_SOURCES ${ATLAS_CORE_SOURCES})
    set(TEST_LIBS m ${BLAS_LINK_LIBS})
    
    # Context API tests
    add_executable(tests_ctx tests/tests_ctx.c ${TEST_SOURCES})
    target_link_libraries(tests_ctx ${TEST_LIBS})
    
    add_executable(tests_ctx_v03 tests/tests_ctx_v03.c ${TEST_SOURCES})
    target_link_libraries(tests_ctx_v03 ${TEST_LIBS})
    
    add_executable(tests_ctx_v04 tests/tests_ctx_v04.c ${TEST_SOURCES})
    target_link_libraries(tests_ctx_v04 ${TEST_LIBS})
    
    # Enable testing
    enable_testing()
    add_test(NAME tests_ctx COMMAND tests_ctx)
    add_test(NAME tests_ctx_v03 COMMAND tests_ctx_v03)
    add_test(NAME tests_ctx_v04 COMMAND tests_ctx_v04)
endif()

# Print configuration summary
message(STATUS "")
message(STATUS "========================================")
message(STATUS "Atlas Bridge v${PROJECT_VERSION} Configuration")
message(STATUS "========================================")
message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
message(STATUS "C compiler: ${CMAKE_C_COMPILER}")
message(STATUS "BLAS: ${USE_BLAS} (${BLAS_LINK_LIBS})")
message(STATUS "AVX2: ${USE_AVX2}")
message(STATUS "Shared library: ${BUILD_SHARED_LIBS}")
message(STATUS "Static library: ${BUILD_STATIC_LIBS}")
message(STATUS "Tests: ${BUILD_TESTS}")
message(STATUS "========================================")
message(STATUS "")

# Usage instructions
message(STATUS "Build instructions:")
message(STATUS "  mkdir build && cd build")
message(STATUS "  cmake ..")
message(STATUS "  make")
message(STATUS "")
message(STATUS "To disable BLAS: cmake -DUSE_BLAS=OFF ..")
message(STATUS "To disable AVX2: cmake -DUSE_AVX2=OFF ..")
message(STATUS "")
