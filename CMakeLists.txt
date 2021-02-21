cmake_minimum_required(VERSION 3.3)

project(llvm-mutaet)

set(CMAKE_BUILD_TYPE Debug)
set(CMAKE_C_FLAGS "-fPIC")
set(CMAKE_CXX_FLAGS "-fPIC -fno-rtti -std=c++17")

find_package(LLVM 11 REQUIRED)
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")

include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_subdirectory(Mutate)

INSTALL_PROGRAMS(/bin llvm-mutate)
