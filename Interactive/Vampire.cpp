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
#include "Kernel/Problem.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Options.hpp"

#include "Vampire.hpp"

namespace Vampire {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

ScopedPtr<Kernel::Problem> prb;

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


} //namespace Vampire
