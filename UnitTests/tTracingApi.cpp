/**
 * @file tTracingApi.cpp
 * Test for Api::Tracing
 */

#include "Api/Tracing.hpp"

#include "Debug/Log.hpp"


#include "Test/UnitTesting.hpp"

#define UNIT_ID tracing_api
UT_CREATE;

using namespace std;
using namespace Api;



TEST_FUN(trapi1)
{
  ASS(!TAG_ENABLED("test_tag"));
  Tracing::pushTracingState();
  ASS(!TAG_ENABLED("test_tag"));
  Tracing::enableTrace("test_tag");
  ASS(TAG_ENABLED("test_tag"));
  Tracing::popTracingState();
  ASS(!TAG_ENABLED("test_tag"));

  Tracing::pushTracingState();
  Tracing::processTraceString("test_tag");
  ASS(TAG_ENABLED("test_tag"));
  Tracing::popTracingState();
  ASS(!TAG_ENABLED("test_tag"));
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
