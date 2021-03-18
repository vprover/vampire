cmake_minimum_required (VERSION 3.13)

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
)

message("compiler: " ${CMAKE_CXX_COMMAND})


# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})


add_executable(subsat
    subsat_main.cpp
    subsat.cpp
    subsat.hpp
    subsat_config.hpp
    constraint.cpp
    constraint.hpp
    decision_queue.hpp
    default_init_allocator.hpp
    log.cpp
    log.hpp
    SubstitutionTheory.hpp
    types.cpp
    types.hpp
    variable_domain_size.hpp
    vector_map.hpp
)

target_compile_definitions(subsat PRIVATE SUBSAT_STANDALONE=1)

# set(SUBSAT_SANITIZER_FLAGS "-fsanitize=undefined,address,integer")
# target_compile_options(subsat PRIVATE "$<$<CONFIG:DEBUG>:${SUBSAT_SANITIZER_FLAGS}>")
# target_link_options(subsat PRIVATE "$<$<CONFIG:DEBUG>:${SUBSAT_SANITIZER_FLAGS}>")
