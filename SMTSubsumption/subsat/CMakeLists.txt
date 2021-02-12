cmake_minimum_required (VERSION 3.5.1)

project(VampireSubSAT)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DVDEBUG=1 -DUNIX_USE_SIGALRM=1 -DGNUMP=0 ")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -DVDEBUG=0")

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_compile_options(
    # "-ftrapv"
    # "-pedantic"
    # "-Wall"
    # "-Wextra"
    # "-Wconversion"
    # "$<$<CONFIG:DEBUG>:-fsanitize=undefined>"
    # "$<$<CONFIG:DEBUG>:-fsanitize=integer>"
    # "$<$<CONFIG:DEBUG>:-fsanitize=address>"
    # "$<$<CONFIG:DEBUG>:-O0>"
    # "$<$<CONFIG:RELEASE>:-O3>"
)

message("compiler: " ${CMAKE_CXX_COMMAND})


# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})


add_executable(subsat
    subsat.cpp
    subsat.hpp
)

target_compile_definitions(subsat PRIVATE SUBSAT_STANDALONE=1)
