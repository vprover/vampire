################################################################
# general configuration
################################################################
cmake_minimum_required (VERSION 3.14.0)

project(Vampire)

# version
set(VAMPIRE_VERSION_NUMBER 5.0.1)

include(CheckSymbolExists)
include(CTest)
include(cmake/sources.cmake)

find_package(Git QUIET)

# require the compiler to use C++17
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# compile command database
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# we use threads, make sure we link the thread-support stuff
find_package(Threads REQUIRED)
link_libraries(Threads::Threads)

# set build type if not set
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "build type" FORCE)
endif()
message(STATUS "CMAKE_BUILD_TYPE: " ${CMAKE_BUILD_TYPE} " (options: Release (default), Debug, RelWithDebInfo)")

option(BUILD_SHARED_LIBS "build Vampire with dynamic linking" ON)
if (NOT BUILD_SHARED_LIBS)
  set(CMAKE_FIND_LIBRARY_SUFFIXES .a)
  set(CMAKE_EXE_LINKER_FLAGS -static)
endif()
message(STATUS "BUILD_SHARED_LIBS: " ${BUILD_SHARED_LIBS})

# enable CCache if available
find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
  message(STATUS "found ccache, enabling for this build")
  set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_PROGRAM}")
  message(STATUS "CCACHE_PROGRAM: " ${CCACHE_PROGRAM})
endif()

################################################################
# compiler configuration
################################################################

# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

add_compile_definitions(ABSOLUTE_SOURCE_DIR="${CMAKE_SOURCE_DIR}")

if(CMAKE_BUILD_TYPE STREQUAL Debug)
  add_compile_definitions(VDEBUG=1)
else()
  add_compile_definitions(VDEBUG=0)
endif()


option(CHECK_LEAKS "try to free more memory" OFF)
if(CHECK_LEAKS)
  message(STATUS "CHECK_LEAKS = 1")
  add_compile_definitions(CHECK_LEAKS=1)
else()
  add_compile_definitions(CHECK_LEAKS=0)
endif()

option(TIME_PROFILING "enable internal profiler" OFF)
if(TIME_PROFILING)
  message(STATUS "VTIME_PROFILING = 1")
  add_compile_definitions(VTIME_PROFILING=1)
else()
  add_compile_definitions(VTIME_PROFILING=0)
endif()

# Cygwin-specific
if(CYGWIN)
  add_compile_definitions(_BSD_SOURCE)
  # somehow Cygwin fails to link, saying that we have multiple definitions of some (inline) functions
  add_link_options(LINKER:--allow-multiple-definition)
  # link libstdc++ and libgcc statically
  add_link_options(-static-libgcc -static-libstdc++)
  # apparently Cygwin's libc cannot be statically linked, so we have to ship cygwin.dll
endif()

# below here configure flags for specific compilers

if(CMAKE_CXX_COMPILER_ID STREQUAL GNU OR CMAKE_CXX_COMPILER_ID MATCHES Clang$)
  set(GCC_OR_CLANG ON)
endif()

if(GCC_OR_CLANG)
  add_compile_options(-Wall)
  # we don't use multithreaded statics in Vampire
  add_compile_options(-fno-threadsafe-statics)
  # ...or RTTI
  add_compile_options(-fno-rtti)

  if(CMAKE_BUILD_TYPE STREQUAL Debug)
    add_compile_options(-fsanitize=undefined)
    add_link_options(-fsanitize=undefined)
  endif()
endif()

################################################################
# CODE COVERAGE
################################################################

option(COVERAGE "generate code coverage reports" OFF)
if(COVERAGE)
  message(STATUS "Coverage is enabled")
  include(${CMAKE_SOURCE_DIR}/cmake/CodeCoverage.cmake)

  message(STATUS "Removing previous coverage data")
  file(GLOB_RECURSE GCDA_FILES ${CMAKE_BINARY_DIR}/*.gcda)
  file(REMOVE ${GCDA_FILES})

  append_coverage_compiler_flags()
  setup_target_for_coverage_gcovr_html(
    NAME vcoverage
    EXECUTABLE ctest
    EXECUTABLE_ARGS "-j${CMAKE_BUILD_PARALLEL_LEVEL}"
    EXCLUDE "${PROJECT_SOURCE_DIR}/CASC"
      "${PROJECT_SOURCE_DIR}/Debug"
      "${PROJECT_SOURCE_DIR}/UnitTests"
      "${PROJECT_SOURCE_DIR}/Test"
      "${PROJECT_SOURCE_DIR}/cadical"
      "${PROJECT_SOURCE_DIR}/viras"
      "${PROJECT_SOURCE_DIR}/z3")
endif()

################################################################
# VIRAS
################################################################

# attempt to automatically checkout VIRAS
if(GIT_FOUND AND EXISTS "${PROJECT_SOURCE_DIR}/.git" AND NOT EXISTS "${PROJECT_SOURCE_DIR}/viras/.git")
  message(STATUS "VIRAS not checked out, running git submodule update")
  execute_process(
    COMMAND ${GIT_EXECUTABLE} submodule update --init viras
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
  )
endif()

# check for VIRAS
if(NOT EXISTS "${PROJECT_SOURCE_DIR}/viras/README.md")
  message(FATAL_ERROR "VIRAS not found")
endif()

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/viras/src)

################################################################
# GMP
################################################################

# TODO git submodule?
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/mini-gmp-6.3.0)

################################################################
# CaDiCaL
################################################################

# attempt to automatically checkout CaDiCaL
if(GIT_FOUND AND EXISTS "${PROJECT_SOURCE_DIR}/.git" AND NOT EXISTS "${PROJECT_SOURCE_DIR}/cadical/README.md")
  message(STATUS "CaDiCaL not checked out, running git submodule update")
  execute_process(
    COMMAND ${GIT_EXECUTABLE} submodule update --init cadical
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
  )
endif()

# check for CaDiCaL
if(NOT EXISTS "${PROJECT_SOURCE_DIR}/cadical/README.md")
  message(FATAL_ERROR "CaDiCaL not found")
endif()

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/cadical/src)
add_compile_definitions(NBUILD=1)

# Check if closefrom() exists in unistd.h
check_symbol_exists(closefrom "unistd.h" HAVE_CLOSEFROM)
# If closefrom() is missing, define NCLOSEFROM=1
if(NOT HAVE_CLOSEFROM)
    add_compile_definitions(NCLOSEFROM=1)
endif()

################################################################
# Z3
################################################################

# find Z3 automatically
# normally this is just in /z3/build/, but this can be overridden using -DZ3_DIR
find_package(
  Z3
  CONFIG
    NO_CMAKE_PATH
    NO_CMAKE_ENVIRONMENT_PATH
    NO_SYSTEM_ENVIRONMENT_PATH
    NO_CMAKE_PACKAGE_REGISTRY
    NO_CMAKE_SYSTEM_PATH
    NO_CMAKE_SYSTEM_PACKAGE_REGISTRY
    PATHS
      ${Z3_DIR}
      ${CMAKE_SOURCE_DIR}/z3/build/
)

if (Z3_FOUND)
  message(STATUS "found Z3 " ${Z3_VERSION_STRING})
  include_directories(${Z3_CXX_INCLUDE_DIRS})
  link_directories(${Z3_DIR})
  link_libraries(z3)
  add_compile_definitions(VZ3=1)
  set(UNIT_TESTS ${UNIT_TESTS} ${UNIT_TESTS_Z3})
else ()
  message(STATUS "no Z3 found -- compiling without SMT support")
  add_compile_definitions(VZ3=0)
endif()

################################################################
# Vampire
################################################################
# wrap up common object files so not built multiple times for each target
add_library(common OBJECT ${SOURCES})

# the actual Vampire executable
add_executable(vampire vampire.cpp $<TARGET_OBJECTS:common>)

install(TARGETS vampire)

################################################################
# UNIT TESTING
################################################################

if(CMAKE_BUILD_TYPE STREQUAL Debug)
  foreach(test_file ${UNIT_TESTS})
    get_filename_component(test_name ${test_file} NAME_WE)
    string(REGEX REPLACE "^t" "" test_name ${test_name})

    # set UNIT_ID for the unit test
    set_property(SOURCE ${test_file} APPEND PROPERTY COMPILE_DEFINITIONS
      UNIT_ID_STR=\"${test_name}\"
      UNIT_ID=${test_name}
    )
    # register it with CTest
    add_test(${test_name} ${CMAKE_BINARY_DIR}/vtest run ${test_name})
    if(COVERAGE)
      # coverage is a lot slower, so increase the timeout
      set_tests_properties(${test_name} PROPERTIES TIMEOUT 180)
    else()
      set_tests_properties(${test_name} PROPERTIES TIMEOUT 60)
    endif()
  endforeach()

  # build test executable
  add_executable(
    vtest
    EXCLUDE_FROM_ALL # only build when explicitly requested
    ${TESTING_SOURCES}
    ${UNIT_TESTS}
    $<TARGET_OBJECTS:common>
  )
endif()

#################################################################
# automated generation of Vampire revision information from git #
#################################################################
execute_process(
    COMMAND git rev-parse --is-inside-work-tree
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_IS_REPOSITORY
    OUTPUT_STRIP_TRAILING_WHITESPACE
)

if (GIT_IS_REPOSITORY STREQUAL true)
  # VAMPIRE_VERSION_NUMBER and CMAKE_BUILD_TYPE used by version.cpp.in through
  # ConfigureGitVersionCpp.cmake
  add_custom_target(update_git_version ALL
    COMMAND ${CMAKE_COMMAND} -DVAMPIRE_SOURCE_DIR=${CMAKE_SOURCE_DIR}
                  -DVAMPIRE_VERSION_NUMBER=${VAMPIRE_VERSION_NUMBER}
                  -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE}
                  -P ${CMAKE_SOURCE_DIR}/cmake/ConfigureGitVersionCpp.cmake
    BYPRODUCTS version.cpp
    VERBATIM
  )
else()
  configure_file(version.cpp.in version.cpp)
endif()

################################################################
# subsat
################################################################

# standalone version of the SAT solver used for subsumption (resolution)
add_executable(subsat
    EXCLUDE_FROM_ALL  # only build when explicitly requested
    SATSubsumption/subsat/subsat_main.cpp
    $<TARGET_OBJECTS:common>
)
