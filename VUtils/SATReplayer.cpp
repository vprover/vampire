
/*
 * File SATReplayer.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file SATReplayer.cpp
 * Implements class SATReplayer.
 */

#include <fstream>

#include "Lib/Environment.hpp"

#include "SAT/TWLSolver.hpp"

#include "Test/RecordingSatSolver.hpp"

#include "SATReplayer.hpp"

namespace VUtils
{

using namespace Lib;
using namespace SAT;

int SATReplayer::perform(int argc, char** argv)
{
  CALL("SATReplayer::perform");

  if(argc!=4) {
    cerr << "invalid command line"<<endl<<
	    "Usage:"<<endl<<
	    argv[0]<<" "<<argv[1]<<" <prefix> <file name>"<<endl;
    exit(1);
  }

  vstring prefix = vstring(argv[2])+" ";
  ifstream inp(argv[3]);

  TWLSolver solver(*env.options, true);
  Test::SolverReplayer replayer(solver);
  replayer.runFromStream(inp, prefix);

  return 0;
}

}
