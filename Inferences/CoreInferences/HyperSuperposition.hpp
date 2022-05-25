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
 * @file HyperSuperposition.hpp
 * Defines class HyperSuperposition
 *
 */

#ifndef __HyperSuperposition__
#define __HyperSuperposition__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class HyperSuperposition
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(HyperSuperposition);
  USE_ALLOCATOR(HyperSuperposition);

  HyperSuperposition() : _index(0) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* premise);

  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
private:
  typedef pair<TermList,TermList> TermPair;
  /** The int here is a variable bank index of the term's variables */
  typedef pair<TermPair, int> RewriterEntry;
  typedef Stack<RewriterEntry> RewriterStack;

  /**
   * Used for returning the results internally. The first clause is after applying the rewriting
   * and the second is after the simplification we were aiming for is done.
   */
  typedef pair<Clause*,Clause*> ClausePair;
  typedef Stack<ClausePair> ClausePairStack;

  bool tryToUnifyTwoTermPairs(RobSubstitution& subst, TermList tp1t1, int bank11,
      TermList tp1t2, int bank12, TermList tp2t1, int bank21, TermList tp2t2, int bank22);

  bool tryMakeTopUnifiableByRewriter(TermList t1, TermList t2, int t2Bank, int& nextAvailableBank, ClauseStack& premises,
      RewriterStack& rewriters, RobSubstitution& subst, Color& infClr);

  bool tryGetRewriters(Term* t1, Term* t2, int t2Bank, int& nextAvailableBank, ClauseStack& premises,
      RewriterStack& rewriters, RobSubstitution& subst, Color& infClr);

  void tryUnifyingSuperpositioins(Clause* cl, unsigned literalIndex, Term* t1, Term* t2,
      bool disjointVariables, ClauseStack& acc);

  bool tryGetUnifyingPremises(Term* t1, Term* t2, Color clr, bool disjointVariables, ClauseStack& premises);

  /**
   * premises should contain any other premises that can be needed
   * (e.g. an unit literal to resolve with)
   */
  Clause* tryGetContradictionFromUnification(Clause* cl, Term* t1, Term* t2, bool disjointVariables, ClauseStack& premStack);

  bool trySimplifyingFromUnification(Clause* cl, Term* t1, Term* t2, bool disjointVariables, ClauseStack& premStack,
      Clause*& replacement, ClauseIterator& premises);
  bool tryUnifyingNonequalitySimpl(Clause* cl, Clause*& replacement, ClauseIterator& premises);
  bool tryUnifyingToResolveSimpl(Clause* cl, Clause*& replacement, ClauseIterator& premises);


  Literal* getUnifQueryLit(Literal* base);
  void resolveFixedLiteral(Clause* cl, unsigned litIndex, ClausePairStack& acc);

  void tryUnifyingNonequality(Clause* cl, unsigned literalIndex, ClausePairStack& acc);
  void tryUnifyingToResolveWithUnit(Clause* cl, unsigned literalIndex, ClausePairStack& acc);

  static bool rewriterEntryComparator(RewriterEntry p1, RewriterEntry p2);

  UnitClauseLiteralIndex* _index;
};

};

#endif /*__HyperSuperposition__*/
