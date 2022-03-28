cmake_minimum_required (VERSION 3.12.0)

# require the compiler to use C++14
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

project(vampire-examples)

if(DEFINED Vampire_DIR)
    set(ENABLE_VAMPIRE ON)
endif()

if(ENABLE_VAMPIRE)
    find_library(VAMPIRE_LIB vampire HINTS ${Vampire_DIR} $ENV{HOME}/vampire_code_test PATH_SUFFIXES lib bin)

    find_path(VAMPIRE_INCLUDE_DIRS Solver.hpp HINTS ${Vampire_DIR}/../Api $ENV{HOME}/vampire_code_test PATH_SUFFIXES include)

    message(${Vampire_DIR})

    if(VAMPIRE_INCLUDE_DIRS STREQUAL "VAMPIRE_INCLUDE_DIRS-NOTFOUND")
        message(FATAL_ERROR "Could not find vampire include headers, please check Vampire_DIR")
    endif()

    if(VAMPIRE_LIB STREQUAL "VAMPIRE_LIB-NOTFOUND")
        message(FATAL_ERROR "Could not find libvampire, please check Vampire_DIR")
    endif() 

    message(${VAMPIRE_INCLUDE_DIRS})

    set(EXAMPLES_BIN_DIR ${CMAKE_BINARY_DIR}/bin)

    add_executable(ArithmeticReasoning ArithmeticReasoning.cpp)
    add_executable(CeilGreaterThanEqualNum CeilGreaterThanEqualNum.cpp)
    add_executable(SimpleProof SimpleProof.cpp)    

    target_include_directories(ArithmeticReasoning
            PRIVATE ${VAMPIRE_INCLUDE_DIRS})
    target_include_directories(CeilGreaterThanEqualNum
            PRIVATE ${VAMPIRE_INCLUDE_DIRS})
    target_include_directories(SimpleProof
            PRIVATE ${VAMPIRE_INCLUDE_DIRS})

    target_link_libraries(ArithmeticReasoning "${VAMPIRE_LIB}")
    target_link_libraries(CeilGreaterThanEqualNum "${VAMPIRE_LIB}")
    target_link_libraries(SimpleProof "${VAMPIRE_LIB}")


    set_target_properties(ArithmeticReasoning PROPERTIES
      RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_BIN_DIR}
    )

    set_target_properties(CeilGreaterThanEqualNum PROPERTIES
      RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_BIN_DIR}
    )

    set_target_properties(SimpleProof PROPERTIES
      RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_BIN_DIR}
    )
endif()
