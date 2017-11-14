
/*
 * File SMTLIBConcat.hpp.
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
 * @file SMTLIBConcat.hpp
 * Defines class SMTLIBConcat.
 */

#ifndef __SMTLIBConcat__
#define __SMTLIBConcat__

#include "Forwards.hpp"

#include "Shell/LispParser.hpp"

namespace VUtils {

using namespace Lib;
using namespace Shell;

class SMTLIBConcat {
public:
  int perform(int argc, char** argv);

private:
  void rewriteIntsToReals(LExpr* e);

  LExpr* extrafuns2decl(LExpr*);
  void rewriteSmt1FormToSmt2(LExpr* e);
//  LExpr* smtlibToSmtlib2(LExpr* e);

  void addBenchmark(LExpr* expr, DHSet<vstring>& funSet, LispListWriter& wrt);

  LExpr* parseFile(vstring fname);
  LExpr* mergeBenchmarksIntoSmtlib2(Stack<LExpr*>& exprs);
};

}

#endif // __SMTLIBConcat__
