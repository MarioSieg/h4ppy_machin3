# (c) Copyright 2022/23 anonymous author: "VEX", Germany
# I do NOT take any responsibility or guarantee, see LICENSE.md!
# This m_code was made for EDUCATIONAL purposes ONLY!

cmake_minimum_required(VERSION 3.16)

project(happy_machine LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED TRUE)

file(
    GLOB_RECURSE SOURCES
    src/*.hpp
    src/*.cpp
    src/*.inl
)

add_executable(happy_machine ${SOURCES})
add_executable(happy_machine_tests tests/tests.cpp)
