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
#include <csignal>

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

bool popTheories(unsigned popCnt) {
  bool res = UIHelper::popLoadedPieces(popCnt);
  prb = UIHelper::getInputProblem();
  return res;
}

static int last_signal = 0;
static pid_t proving_child = 0;
static std::string last_output;

int lastSignal() {
  return last_signal;
}

static std::filesystem::path path;

static void retrieveOutput() {
  std::ifstream file(path);
  if (!file) {
    last_output = "ERROR: Could not read from output temporary " + path.string();
  } else {
    std::ostringstream ss;
    ss << file.rdbuf();
    last_output = ss.str();
  }
}

std::string getSolution() {
  return last_output;
}

ProverStatus getStatus() {
  if (proving_child == 0) {
    return ProverStatus::READY;
  }

  int status;

  std::cout << "getStatus on child: " << proving_child << " and status is " << status << std::endl;

  pid_t result = waitpid(proving_child, &status, WNOHANG);

  std::cout << "waitpid returned " << result << " and status is " << status << std::endl;

  if (result == 0) {
      return ProverStatus::RUNNING;
  } else if (result == proving_child) {
      proving_child = 0; // or could signalled be still revived? (e.g. after CTRL+Z?)
      // Child has exited (or changed state)
      if (WIFEXITED(status)) {
          int exit_code = WEXITSTATUS(status);
          if (exit_code == 0) {
            retrieveOutput();

            std::cout << " which meant SUCCEEDED" << std::endl;

            return ProverStatus::SUCCEEDED;
          } else {

            std::cout << " which meant FAILED" << std::endl;

            retrieveOutput();
            return ProverStatus::FAILED;
          }
      } else if (WIFSIGNALED(status)) {
          last_signal = WTERMSIG(status);

          std::cout << " which meant SIGNALLED with " << last_signal << std::endl;

          return ProverStatus::SIGNALLED;
      }
  } else if (result == -1) {

      std::cout << " which meant waitpid error" << std::endl;

      perror("waitpid");
  }
  return ProverStatus::ERROR;
}

bool stopProver() {
  if (proving_child == 0) {
    return false;
  } else {
    int res = ::kill(proving_child, SIGINT);
    return res == 0;
    // if(res!=0) {
    //   ASS_EQ(res,-1);
    //   SYSTEM_FAIL("Call to kill() function failed.", errno);
    // }
  }
}

bool runProver(std::string query, std::string config) {
  Options& opts = *Lib::env.options;

  if (proving_child) {
    std::cout << "runProver will Fail, proving_child is already set to " << proving_child << std::endl;
    return false;
  }

  path = fs::temp_directory_path() / "vampire-output";

  std::cout << "our path is " << path << std::endl;

  pid_t process = Lib::Sys::Multiprocessing::instance()->fork();
  ASS_NEQ(process, -1);
  if(process == 0) {
    UIHelper::unsetExpecting(); // probably garbage at this point

    std::ofstream output(path);

    Stack<std::string> pieces;
    StringUtils::splitStr(config.c_str(),' ',pieces);
    StringUtils::dropEmpty(pieces);
    Stack<const char*> argv(pieces.size()+1);
    argv.push("./vampire"); // vampire expects argv[0] to be the executable (it will mostly ignore)
    for(auto it = pieces.iterFifo(); it.hasNext();) {
      argv.push(it.next().c_str());
    }
    Shell::CommandLine cl(argv.size(), argv.begin());
    cl.interpret(opts);

    Timer::reinitialise(); // start our timer (in the child)
    Timer::setOutput(output);

    loadTPTP("query",query);

    /*
    if (!opts.inputFile().empty()) {
      UIHelper::parseFile(opts.inputFile(),opts.inputSyntax(),true);
      prb = UIHelper::getInputProblem();
    }
    */

    dispatchByMode(prb.release(), output); // we release, otherwise the child will try to delete this in the end, which will break
    exit(vampireReturnValue);
  } else {
    // remember our child; it also means that we are busy proving
    proving_child = process;

    std::cout << "success, runProver got a new child: " << proving_child << std::endl;
  }
  return true;
}


} //namespace Vampire
