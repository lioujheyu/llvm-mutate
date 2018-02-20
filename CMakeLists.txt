cmake_minimum_required(VERSION 3.3)

set(CMAKE_C_FLAGS "-fPIC")
set(CMAKE_CXX_FLAGS "-fPIC -fno-rtti -std=c++11")

find_package(LLVM)

include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_subdirectory(Mutate)

INSTALL_PROGRAMS(/bin llvm-mutate)
