cmake_minimum_required(VERSION 3.1)
project(Skeleton)

# support C++14 features used by LLVM 10.0.0
set(CMAKE_CXX_STANDARD 14)

#find_package(LLVM REQUIRED CONFIG)
find_package(LLVM 11.0 CONFIG)
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_subdirectory(skeleton)  # Use your pass name here.
