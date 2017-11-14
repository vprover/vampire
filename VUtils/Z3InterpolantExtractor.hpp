
/*
 * File Z3InterpolantExtractor.hpp.
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
 * @file Z3InterpolantExtractor.hpp
 * Defines class Z3InterpolantExtractor.
 */

#ifndef __Z3InterpolantExtractor__
#define __Z3InterpolantExtractor__

#include <utility>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"

#include "Shell/LispParser.hpp"

#include "RangeColoring.hpp"


namespace VUtils {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class ZIE {
public:
  LExpr* getInput();
  int perform(int argc, char** argv);


private:
  bool _showInterpolants;

private:
  Unit* getZ3Refutation();


  static vstring hypothesesToString(List<TermList>* hypotheses);

  struct ProofObject {
    ProofObject() {}
    ProofObject(Unit* unit, List<TermList>* hypotheses)
    : unit(unit), hypotheses(hypotheses) {}

    vstring hypothesesToString()
    { return ZIE::hypothesesToString(hypotheses); }

    Unit* unit;
    List<TermList>* hypotheses;
  };

  unsigned getFunctionNumber(vstring fnName, unsigned arity);

  bool tryReadNumber(LExpr* expr, TermList& res);

  bool isTermVariable(vstring name) { return name[0]=='$' || name[0]=='?'; }
  bool isProofVariable(vstring name) { return name[0]=='@'; }

  bool readLet(LExpr* expr, LExpr*& tail);
  void processLets();

  TermList negate(TermList term);

  TermList readTerm(LExpr* term);
  ProofObject readProofObject(LExpr* term);

  TermList getTermAssignment(vstring name);
  ProofObject getProofObjectAssignment(vstring name);

  Formula* termToFormula(TermList trm);
  Formula* termToFormula(TermList trm, List<TermList>* hypotheses);

  void resolveHypotheses(List<TermList>*& hypotheses, TermList lemma);

  typedef pair<vstring,LExpr*> LetRecord;
  Stack<LetRecord> _letRecords;

  DHMap<vstring, TermList> _termAssignments;
  DHMap<vstring, ProofObject> _proofAssignments;

  /**
   * All units in the proof.
   *
   * Consequences are closer to the top of the stack than their
   * premises.
   */
  UnitStack _allUnits;
  UnitStack _allUnitsColored;
  UnitStack _allUnitsLocal;


  UnitStack _inputUnits;
private:

  struct UnaryFunctionInfo
  {
    UnaryFunctionInfo() {}
    UnaryFunctionInfo(TermList firstArg);

    void onNewArg(TermList firstArg);

    bool numericArgsOnly;

    IntegerConstantType minArg;
    IntegerConstantType maxArg;
  };

  void onFunctionApplication(TermList fn);

  typedef DHMap<unsigned, UnaryFunctionInfo> UnaryInfoMap;
  UnaryInfoMap _unaryFnInfos;

  bool colorProof(TermColoring& colorer, UnitStack& derivation, UnitStack& coloredDerivationTgt);

  void collectSMTLIB1FileFunctionNames(const char* fname, DHSet<vstring>& acc);

  TermColoring* createRangeColorer();
  TermColoring* createFileColorer(unsigned leftCnt, char** leftFNames, unsigned rightCnt, char** rightFNames);

  TermColoring* createColorer(unsigned argc, char** argv);
private:
  void outputInterpolantStats(Unit* refutation);
};

}

#endif // __Z3InterpolantExtractor__
