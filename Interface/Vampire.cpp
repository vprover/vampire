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

#include "Vampire.hpp"
#include "Modes.hpp"

#include <sys/wait.h>

#include <filesystem>
namespace fs = std::filesystem;
#include <fstream>

#include "Lib/ScopedPtr.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/Options.hpp"
#include "Shell/CommandLine.hpp"


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

static int last_signal = 0;
static pid_t proving_child = 0;

ProverStatus getStatus() {
  if (proving_child == 0) {
    return ProverStatus::READY;
  }

  int status;
  pid_t result = waitpid(proving_child, &status, WNOHANG);

  if (result == 0) {
      return ProverStatus::RUNNING;
  } else if (result == proving_child) {
      // Child has exited (or changed state)
      if (WIFEXITED(status)) {
          int exit_code = WEXITSTATUS(status);
          if (exit_code == 0) {
            return ProverStatus::SUCCEEDED;
          } else {
            return ProverStatus::FAILED;
          }
      } else if (WIFSIGNALED(status)) {
          last_signal = WTERMSIG(status);
          return ProverStatus::SIGNALLED;
      }
  } else if (result == -1) {
      perror("waitpid");
  }
  return ProverStatus::ERROR;
}

static std::filesystem::path path;

bool runProver(std::string commandLine) {
  Options& opts = *Lib::env.options;

  if (!proving_child) {
    return false;
  }

  path = fs::temp_directory_path() / "vampire-output";

  pid_t process = Lib::Sys::Multiprocessing::instance()->fork();
  ASS_NEQ(process, -1);
  if(process == 0) {
    UIHelper::unsetExpecting(); // probably garbage at this point

    std::ofstream output(path);

    Stack<std::string> pieces;
    StringUtils::splitStr(commandLine.c_str(),' ',pieces);
    StringUtils::dropEmpty(pieces);
    Stack<const char*> argv(pieces.size());
    for(auto it = pieces.iterFifo(); it.hasNext();) {
      argv.push(it.next().c_str());
    }
    Shell::CommandLine cl(argv.size(), argv.begin());
    cl.interpret(opts);

    Timer::reinitialise(); // start our timer (in the child)

    if (!opts.inputFile().empty()) {
      UIHelper::parseFile(opts.inputFile(),opts.inputSyntax(),true);
      prb = UIHelper::getInputProblem();
    }

    dispatchByMode(prb.ptr(), output);
    exit(vampireReturnValue);
  } else {
    // remember our child; it also means that we are busy proving
    proving_child = process;
  }
  return true;
}


} //namespace Vampire
