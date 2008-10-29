/**
 * @file sat.cpp. Implements the top-level procedures of Vampire's SAT
 * solver.
 */

#include <iostream>
// #include <calloc>

#include "Lib/Random.hpp"

using namespace std;

/**
 * The main function.
  * @since 03/12/2003 many changes related to logging 
  *        and exception handling.
  * @since 10/09/2004, Manchester changed to use knowledge bases
  */
int main (int argc, char* argv [])
{
//   CALL ("main");

//   void* q = new char[1048544];
  for (int i = 1; i < 100; i++) {
//     void* q = malloc(Lib::Random::getInteger(1048544));
    void* q = malloc(4088);
    cout << q << "\n";
  }

  return EXIT_SUCCESS;
} // main

