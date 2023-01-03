# (c) Copyright 2022/23 anonymous author: "VEX", Germany
# I do NOT take any responsibility or guarantee, see LICENSE.md!
# This m_code was made for EDUCATIONAL purposes ONLY!

cmake_minimum_required(VERSION 3.16)

project(happy_machine LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED TRUE)

if (CMAKE_BUILD_TYPE STREQUAL "Release")
    set (IS_RELEASE true)
    set (IS_DEBUG false)
else ()
    set (IS_RELEASE false)
    set (IS_DEBUG true)
endif ()

if (WIN32) # Clang-CL only, no MSVC support
    add_compile_options(/EHs /Oy /Oi /fp:fast)
    if (${IS_RELEASE})
        add_compile_options(/EHs /Oy /Oi /fp:fast /GL -Ofast)
        add_link_options(/LTCG)
    endif ()
endif()

file(
    GLOB_RECURSE SOURCES
    src/*.hpp
    src/*.cpp
    src/*.inl
)

add_library(lib_happy_machine STATIC ${SOURCES})
add_executable(happy_machine src/main.cpp)
target_link_libraries(happy_machine lib_happy_machine)
add_executable(happy_machine_tests tests/tests.cpp)
target_link_libraries(happy_machine_tests lib_happy_machine)
