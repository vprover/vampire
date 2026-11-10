/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Shell/Options.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Shell;

bool testGlobal(Options& o)
{
  try{
    return o.checkGlobalOptionConstraints();
  }
  catch(Lib::UserErrorException& e){
    e.cry(cout);
    return false;
  }
}

bool testOption(bool bad, std::string name,std::string value)
{
    //cout << (bad ? "Should be bad" : "Should be good") << endl;
    Options options;
    options.set(name,value);
    bool res = testGlobal(options);
    if(bad) res = !res;
    return res;
}
bool testOptionBad(std::string name, std::string value){ return testOption(true,name,value); }
bool testOptionGood(std::string name, std::string value){ return testOption(false,name,value); }


TEST_FUN(int_bounds)
{
  ASS(testOptionBad("naming","327681"));
  ASS(testOptionGood("naming","32767"));
  ASS(testOptionBad("lrs_first_time_check","200"));
  ASS(testOptionBad("lrs_first_time_check","-200"));
  ASS(testOptionGood("lrs_first_time_check","50"));
  ASS(testOptionBad("extensionality_max_length","1"));
}

TEST_FUN(default_dependence)
{
  // we shouldn't just be able to set extensionality_allow_pos_eq to true,
  // since it does no make sense, unless extensionality_resolution is something else than the (default) off
  ASS(testOptionBad("extensionality_allow_pos_eq","true"));
}

TEST_FUN(decode_rejects_empty_strategy)
{
  Options options;
  try {
    options.readFromEncodedOptions("");
  } catch (Lib::UserErrorException& e) {
    ASS_EQ(e.msg(), "bad test id ");
    return;
  }
  ASSERTION_VIOLATION;
}

TEST_FUN(decode_rejects_unknown_strategy)
{
  Options options;
  try {
    options.readFromEncodedOptions("unknown");
  } catch (Lib::UserErrorException& e) {
    ASS_EQ(e.msg(), "bad test id unknown");
    return;
  }
  ASSERTION_VIOLATION;
}

TEST_FUN(decode_accepts_valid_strategy)
{
  Options options;
  options.readFromEncodedOptions("dis+10_2:3_50");
  ASS_EQ(options.saturationAlgorithm(), Options::SaturationAlgorithm::DISCOUNT);
  ASS_EQ(options.selection(), 10);
  ASS_EQ(options.ageRatio(), 2);
  ASS_EQ(options.weightRatio(), 3);
  ASS_EQ(options.timeLimitInDeciseconds(), 50);
}
