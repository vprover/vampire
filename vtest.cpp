
/*
 * File vtest.cpp.
 *
 * This file is part of the source code of the software
 * program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 *
 * This source code is distributed under the licence found here
 *
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but
 * not allowed to distribute, modify, copy, create derivatives,
 * or use in
 * competitions. 
 * For other uses of Vampire please contact developers for a
 * different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file vtest.cpp
 * Provides main function for the vtest executable which is used for unit
 * testing.
 */

#include "Forwards.hpp"

//#include "Api/ResourceLimits.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/System.hpp"

#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Test/UnitTesting.hpp"

#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

using namespace Lib;
using namespace Kernel;
using namespace Test;

UnitList *globUnitList = 0;
int globReturnValue = 1;

void explainException(Exception &exception) {
  exception.cry(cout);
} // explainException

void readAndFilterGlobalOpts(Stack<char *> &args) {
  Stack<char *>::StableDelIterator it(args);

  // skip the first item which is the executable name
  ALWAYS(it.hasNext());
  it.next();

  while (it.hasNext()) {
    vstring arg(it.next());
    if (arg == "-tr") {
      it.del();
      if (!it.hasNext()) {
        USER_ERROR("value for -tr option expected");
      }
      vstring traceStr(it.next());
      it.del();
      // PROCESS_TRACE_SPEC_STRING(traceStr);
    }
    // this part is added just for testing
    else if (arg == "-t") {
      it.del();
      if (!it.hasNext()) {
        USER_ERROR("value for timelimit expected");
      }
      int seconds;
      Int::stringToInt(it.next(), seconds);
      // Api::ResourceLimits::setLimits(0,seconds*10);
    } else {
      break;
    }
  }
}

int main(int argc, char *argv[]) {
  CALL("main");

  srand(1); // this is for the reproducibility

  // Api::ResourceLimits::disableLimits();
  System::registerArgv0(argv[0]);
  System::setSignalHandlers();
  // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  Stack<char *> args;
  args.loadFromIterator(getArrayishObjectIterator(argv, argc));
  readAndFilterGlobalOpts(args);

  try {

    if (args.size() == 1) {
      UnitTesting::instance()->runAllTests(cout);
    } else if (args.size() == 2 || args.size() == 3) {
      if (!strcmp(args[1], "-l")) {
        UnitTesting::instance()->printTestNames(cout);
      } else {
        if (!UnitTesting::instance()->runTest(args[args.size() - 1], cout)) {
          cout << "Unknown test name: " << args[1] << endl;
          cout << "Run \"" << args[0]
               << " -l\" for the list of available tests." << endl;
        }
      }
    } else {
      cout << "Invalid number of arguments (" << (argc - 1) << ")." << endl;
      cout << "Run \"" << args[0] << "\" to run all available tests." << endl;
      cout << "Run \"" << args[0] << " <test_id>\" to run a single test."
           << endl;
      cout << "Run \"" << args[0] << " -l\" for the list of available tests."
           << endl;
    }

#if CHECK_LEAKS
    if (globUnitList) {
      MemoryLeak leak;
      leak.release(globUnitList);
    }
    delete env.signature;
    env.signature = 0;
#endif

    // if we got here, all went well and we can return 0
    globReturnValue = 0;
  }
#if VDEBUG
  catch (Debug::AssertionViolationException &exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
  }
#endif
  catch (UserErrorException &exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  } catch (Exception &exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
    env.statistics->print(cout);
  } catch (std::bad_alloc &_) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    cout << "Insufficient system memory" << '\n';
  }
  //   delete env.allocator;

  return globReturnValue;
}
