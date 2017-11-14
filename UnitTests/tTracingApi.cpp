
/*
 * File tTracingApi.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file tTracingApi.cpp
 * Test for Api::Tracing
 */
/*
#include "Api/Tracing.hpp"


#include "Test/UnitTesting.hpp"

#define UNIT_ID tracing_api
UT_CREATE;

using namespace std;
using namespace Api;



TEST_FUN(trapi1)
{
  Tracing::pushTracingState();
  Tracing::enableTrace("test_tag");
  Tracing::popTracingState();

  Tracing::pushTracingState();
  Tracing::processTraceString("test_tag");
  Tracing::popTracingState();
}

TEST_FUN(trapiEx1)
{
  //popping without pushing should throw exception
  try {
    Tracing::popTracingState();
    ASSERTION_VIOLATION;
  }
  catch(...) {}
}
*/
