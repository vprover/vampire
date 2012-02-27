/**
 * @file SimpleSMT.cpp
 * Implements class SimpleSMT.
 */

#include "Debug/Tracer.hpp"

#include "SimpleSMT.hpp"

namespace VUtils
{

int SimpleSMT::perform(int argc, char** argv)
{
  CALL("SimpleSMT::perform");

  string fname = argv[2];

  cout << "Now we should be solving "<<fname<<endl;

  return 0;
}

}
