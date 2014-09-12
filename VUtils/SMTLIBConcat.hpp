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
