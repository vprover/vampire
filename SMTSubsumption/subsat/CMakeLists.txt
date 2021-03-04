cmake_minimum_required (VERSION 3.5.1)

project(VampireSubSAT)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DVDEBUG=1 -DUNIX_USE_SIGALRM=1 -DGNUMP=0 ")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -DVDEBUG=0")

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_compile_options(
    "-ftrapv"
    "-pedantic"
    "-Wall"
    "-Wextra"
    "-Wconversion"
    # "$<$<CONFIG:DEBUG>:-fsanitize=undefined>"
    # "$<$<CONFIG:DEBUG>:-fsanitize=integer>"
    # "$<$<CONFIG:DEBUG>:-fsanitize=address>"
)

message("compiler: " ${CMAKE_CXX_COMMAND})


# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})


add_executable(subsat
    subsat.cpp
    subsat.hpp
    decision_queue.hpp
    default_init_allocator.hpp
    domain_degree.hpp
    types.hpp
    types.cpp
    clause.hpp
    clause.cpp
    vector_map.hpp
    log.hpp
    log.cpp
)

target_compile_definitions(subsat PRIVATE SUBSAT_STANDALONE=1)
