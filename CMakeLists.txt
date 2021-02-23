cmake_minimum_required(VERSION 3.15)

project(llvm-mutaet)

set(CMAKE_BUILD_TYPE Debug)
set(CMAKE_C_FLAGS "-fPIC")
set(CMAKE_CXX_FLAGS "-fPIC -fno-rtti -std=c++17")

find_package(LLVM 11.1.0 REQUIRED)
Message(STATUS "LLVM detection: ${LLVM_VERSION}")
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")

include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_subdirectory(Mutate)

set_target_properties(Mutate PROPERTIES SUFFIX ".so.${LLVM_VERSION_MAJOR}")
set(LLVM_VERSION_STRING ${LLVM_VERSION_MAJOR})
configure_file(_llvm.py.in _llvm.py)

# INSTALL_PROGRAMS(/bin llvm-mutate)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/_llvm.py DESTINATION .)
install(TARGETS Mutate DESTINATION .)
