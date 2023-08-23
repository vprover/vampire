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
 * @file Superposition.hpp
 * Defines class Superposition.
 */


#ifndef __Superposition__
#define __Superposition__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"
#include "Kernel/KBO.hpp"
#include "Lib/MultiCounter.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class LeftmostInnermostReducibilityChecker {
private:
  DHSet<Term*> _reducible;
  DHSet<Term*> _nonReducible;

  DemodulationLHSIndex* _index;
  const Ordering& _ord;
  KBO* _kbo;
  const Options& _opt;

  class SmallerIterator {
  public:
    SmallerIterator(Term* side, Term* sideS, Term* rwTermS, KBO* kbo, const Ordering& ord);

    bool hasNext();
    Term* next();

  private:
    void pushTerms(TermList* orig, TermList* t);

    struct Info {
      Info(size_t v) : w(0), vc(v), nope(false) {}
      unsigned w;
      DArray<unsigned> vc;
      bool nope;
    };

    TermList _rwTerm;
    TermList _side;
    TermList _sideS;
    Stack<std::pair<TermList*,TermList*>> _stack;
    Stack<Info> _infos;
    MultiCounter _rwVarCnts;
    unsigned _maxVar;
    unsigned _rwWeight;
    KBO* _kbo;
    const Ordering& _ord;
    Term* _next;
  };

  bool checkTermReducible(Term* t, TermList* tgtTermS);
  bool checkLeftmostInnermost(Clause* cl, Term* rwTermS, ResultSubstitution* subst, bool result);
  bool checkSmaller(Clause* cl, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result);

public:
  CLASS_NAME(LeftmostInnermostReducibilityChecker);
  USE_ALLOCATOR(LeftmostInnermostReducibilityChecker);

  LeftmostInnermostReducibilityChecker(DemodulationLHSIndex* index, const Ordering& ord, const Options& opt, Problem& prb);

  bool check(Clause* cl, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result);
  void reset() { _nonReducible.reset(); }
  bool isNonReducible(Term* t) const { return _nonReducible.contains(t); }
};

class Superposition
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Superposition);
  USE_ALLOCATOR(Superposition);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);

private:
  Clause* performSuperposition(
    Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
    Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer,
          UnificationConstraintStackSP constraints);

  bool checkClauseColorCompatibility(Clause* eqClause, Clause* rwClause);
  static bool earlyWeightLimitCheck(Clause* eqClause, Literal* eqLit,
      Clause* rwClause, Literal* rwLit, TermList rwTerm, TermList eqLHS, TermList eqRHS,
      ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer, unsigned numPositiveLiteralsLowerBound, const Inference& inf);

  static bool checkSuperpositionFromVariable(Clause* eqClause, Literal* eqLit, TermList eqLHS);

  struct ForwardResultFn;

  struct LHSsFn;
  struct RewritableResultsFn;
  struct BackwardResultFn;

  SuperpositionSubtermIndex* _subtermIndex;
  SuperpositionLHSIndex* _lhsIndex;
};


};

#endif /* __Superposition__ */
