/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file vampire.cpp. Implements the top-level procedures of Vampire.
 */

#include "Interface/Vampire.hpp"
#include "Interface/Modes.hpp"

#include <iostream>
#include <string>

using namespace std;

#if VZ3
#include "z3++.h"
#endif

#include "Lib/Environment.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Timer.hpp"
#include "Lib/System.hpp"

#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/CommandLine.hpp"

#include "Parse/TPTP.hpp"

using namespace Shell;

void explainException(Exception& exception)
{
  exception.cry(std::cout);
} // explainException

void interactiveMetamode()
{
  Options& opts = *env.options;
  opts.setInteractive(false); // so that we don't pass the interactivity on to the workers

  if (!opts.inputFile().empty()) {
    UIHelper::parseFile(opts.inputFile(),opts.inputSyntax(),true);
    opts.resetInputFile();
  } // no parsing of the whole cin in interactiveMetamode

  Vampire::init();

  while (true) {
    std::string line;
    if (!getline(cin, line) || line.rfind("exit",0) == 0) {
      cout << "Bye." << endl;
      break;
    } else if (line.rfind("run",0) == 0) {
      bool res = Vampire::runProver("",line.substr(3));
      cout << "runProver returned " << res << endl;

      // the whole running happens in a child (don't modify our options, don't crash here when parsing option rubbish, etc.)
      /*
      pid_t process = Lib::Sys::Multiprocessing::instance()->fork();
      ASS_NEQ(process, -1);
      if(process == 0) {
        Timer::reinitialise(); // start our timer (in the child)
        UIHelper::unsetExpecting(); // probably garbage at this point

        Stack<std::string> pieces;
        StringUtils::splitStr(line.c_str(),' ',pieces);
        StringUtils::dropEmpty(pieces);
        Stack<const char*> argv(pieces.size());
        for(auto it = pieces.iterFifo(); it.hasNext();) {
          argv.push(it.next().c_str());
        }
        Shell::CommandLine cl(argv.size(), argv.begin());
        cl.interpret(opts);
        if (!opts.inputFile().empty()) {
          UIHelper::parseFile(opts.inputFile(),opts.inputSyntax(),true);
          prb = UIHelper::getInputProblem();
        }
        dispatchByMode(prb.ptr(),std::cout);
        exit(vampireReturnValue);
      }
      */
    } else if (line.rfind("stat",0) == 0) {
      cout << Vampire::getStatus() << endl;
    } else if (line.rfind("stop",0) == 0) {
      cout << Vampire::stopProver() << endl;
    } else if (line.rfind("soln",0) == 0) {
      cout << Vampire::getSolution() << endl;

    } else if (line.rfind("load",0) == 0) {
      Stack<std::string> pieces;
      StringUtils::splitStr(line.c_str(),' ',pieces);
      StringUtils::dropEmpty(pieces);
      auto it = pieces.iterFifo();
      ALWAYS(it.next() == "load");
      while (it.hasNext()) {
        UIHelper::parseFile(it.next(),opts.inputSyntax(),true);
      }
      Vampire::init();
    } else if (line.rfind("tptp ",0) == 0) {
      std::string theory = line.substr(5);
      cout << "loadTPTP returned " << Vampire::loadTPTP(theory,theory) << endl;
    } else if (line.rfind("smt2 ",0) == 0) {
      try {
        std::string theory = line.substr(5);
        UIHelper::parseString(/* we tag the oneliner by itself*/ theory,theory,Options::InputSyntax::SMTLIB2);
      } catch (ParsingRelatedException& exception) {
        explainException(exception);
      }
    } else if (line.rfind("list",0) == 0) {
      auto thList = Vampire::listTheories();
      for (auto thTag : thList) {
        cout << thTag << endl;
      }
    } else if (line.rfind("pop",0) == 0) {
      Stack<std::string> pieces;
      StringUtils::splitStr(line.c_str(),' ',pieces);
      StringUtils::dropEmpty(pieces);
      int numPops = 1;
      if (pieces.size() > 1) {
        Int::stringToInt(pieces[1],numPops);
      }
      Vampire::popTheories(numPops);
    } else {
      cout << "Unreconginzed command! Try 'run [options] [filename_to_load]', 'load <filenames>', 'tptp <one_line_input_in_tptp>',\n"
              "'smt2 <one_line_input_in_smt2>' 'pop [how_many_levels] (one is default)', 'list', or 'exit'." << endl;
    }
  }
}

/**
 * The main function.
 * @since 03/12/2003 many changes related to logging
 *        and exception handling.
 * @since 10/09/2004, Manchester changed to use knowledge bases
 */
int main(int argc, char* argv[])
{
  System::setSignalHandlers();

  try {
    Options& opts = *env.options;

    // read the command line and interpret it
    Shell::CommandLine cl(argc, argv);
    cl.interpret(opts);

#if VDEBUG
    std::cerr << "% WARNING: debug build, do not use in anger\n";
#endif

    if(opts.encodeStrategy()){
      cout << opts.generateEncodedOptions() << "\n";
    }

#if VTIME_PROFILING
    TimeTrace::instance().setEnabled(opts.timeStatistics());
#endif

    // If any of these options are set then we just need to output and exit
    if (opts.showHelp() || opts.showOptions() || opts.showExperimentalOptions() ||
       !opts.explainOption().empty() || opts.printAllTheoryAxioms()) {
      opts.output(std::cout);
      exit(0);
    }

    Lib::setMemoryLimit(env.options->memoryLimit() * 1048576ul);

    if (opts.mode() == Options::Mode::MODEL_CHECK) {
      opts.setOutputAxiomNames(true);
    }

    if (opts.interactive()) {
      interactiveMetamode();
    } else {
      // can only happen after reading options as it relies on `env.options`
      Timer::reinitialise(); // start our timer, so that we also limit parsing

#if VAMPIRE_PERF_EXISTS
      unsigned saveInstrLimit = env.options->instructionLimit();
      if (env.options->parsingDoesNotCount()) {
        env.options->setInstructionLimit(0);
      }
#endif

      if (opts.inputFile().empty()) {
        UIHelper::parseStandardInput(opts.inputSyntax());
      } else {
        UIHelper::parseFile(opts.inputFile(),opts.inputSyntax(),
                            opts.mode() != Options::Mode::SPIDER && opts.mode() != Options::Mode::PROFILE);
      }

#if VAMPIRE_PERF_EXISTS
      if (env.options->parsingDoesNotCount()) {
        Timer::updateInstructionCount();
        unsigned burnedParsing = Timer::elapsedMegaInstructions();

        addCommentSignForSZS(std::cout);
        std::cout << "Instructions burned parsing: " << burnedParsing << " (million)" << endl;

        env.options->setInstructionLimit(saveInstrLimit+burnedParsing);
      }
#endif

      dispatchByMode(UIHelper::getInputProblem(),std::cout);
    }

#if CHECK_LEAKS
    delete env.signature;
    env.signature = 0;
#endif
  }
#if VZ3
  catch (z3::exception& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    if (outputAllowed()) {
      cout << "Z3 exception:\n" << exception.msg() << endl;
    }
    reportSpiderFail();
  }
#endif
  catch (UserErrorException& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
    explainException(exception);
  }
catch (Parse::TPTP::ParseErrorException& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
    explainException(exception);
  }
  catch (Exception& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
    explainException(exception);
  } catch (std::bad_alloc& _) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
    std::cout << "Insufficient system memory" << '\n';
  }

  return vampireReturnValue;
} // main
