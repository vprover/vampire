/**
 * @file tTracingApi.cpp
 * Test for Api::Tracing
 */

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
