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

  string prefix = string(argv[2])+" ";
  ifstream inp(argv[3]);

  TWLSolver solver(*env -> options, true);
  Test::SolverReplayer replayer(solver);
  replayer.runFromStream(inp, prefix);

  return 0;
}

}
