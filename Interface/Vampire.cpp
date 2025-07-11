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
 * @file Vampire.cpp
 * Implements class Vampire.
 */

#include "Lib/ScopedPtr.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/Options.hpp"
#include "Shell/CommandLine.hpp"

#include "Vampire.hpp"
#include "Modes.hpp"

namespace Vampire {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

static ScopedPtr<Kernel::Problem> prb;

void init() {
  prb = UIHelper::getInputProblem();
}

bool loadTPTP(std::string tag, std::string theory) {
  try {
    UIHelper::parseString(tag,theory,Options::InputSyntax::TPTP);
    prb = UIHelper::getInputProblem();
  } catch (ParsingRelatedException&) {
    return false;
  }
  return true;
}

std::vector<std::string> listTheories() {
  return UIHelper::getLoadedPiecesTags();
}

bool popTeories(unsigned popCnt) {
  bool res = UIHelper::popLoadedPieces(popCnt);
  prb = UIHelper::getInputProblem();
  return res;
}

bool runProver(std::string commandLine) {
  Options& opts = *Lib::env.options;

  pid_t process = Lib::Sys::Multiprocessing::instance()->fork();
  ASS_NEQ(process, -1);
  if(process == 0) {
    Timer::reinitialise(); // start our timer (in the child)
    UIHelper::unsetExpecting(); // probably garbage at this point

    Stack<std::string> pieces;
    StringUtils::splitStr(commandLine.c_str(),' ',pieces);
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
    dispatchByMode(prb.ptr());
    exit(vampireReturnValue);
  } else {

  }
}


} //namespace Vampire
