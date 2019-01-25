
/*
 * File Superposition.hpp.
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
 * @file Superposition.hpp
 * Defines class Superposition.
 */


#ifndef __Superposition__
#define __Superposition__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Superposition
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Superposition);
  USE_ALLOCATOR(Superposition);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);

  struct CombResultIterator
  { 
     const int QUERY_BANK = 0;
     const int RESULT_BANK = 1;
     typedef pair<pair<Literal*, TermList>, TermQueryResult> QueryResType;
     
     CombResultIterator(QueryResType arg): _conflictingSorts(false), _arg(arg)
     {  
       //cout << "starting iterator from SUPERPOSITION" << endl;
       TermList t1 = arg.first.second;
       TermList t2 = arg.second.term;
       unsigned t1s = SortHelper::getTermSort(t1, arg.first.first);
       unsigned t2s = SortHelper::getTermSort(t2, arg.second.literal);

  /*
       cout << "Searching for unifiers:" << endl;
       cout << "Lit1 " + arg.first.first->toString() << endl;
       cout << "T1 " + t1.toString() << endl;
       cout << "Clause2 " + arg.second.clause->toString() << endl;
       cout << "Lit2 " + arg.second.literal->toString() << endl;
       cout << "T2 " + t2.toString() + "\n" << endl;
  */

       if(t1s != t2s){
         _conflictingSorts = true;
       } else {
         _csIt = vi(new CombSubstIterator(t1, t1s, QUERY_BANK, t2, t2s, RESULT_BANK)); 
       }
     }

     DECL_ELEMENT_TYPE(QueryResType);
     
     bool hasNext(){
       CALL("Superposition::CombResultIterator::hasNext");
       if(_conflictingSorts){
        return false;
       }
       return _csIt.hasNext();
     }
     
     OWN_ELEMENT_TYPE next(){
       CALL("Superposition::CombResultIterator::next");
       CombSubstitution* cs = _csIt.next();
       ResultSubstitutionSP s = ResultSubstitution::fromSubstitution(cs, QUERY_BANK, RESULT_BANK);
       _arg.second.substitution = s;
       return _arg;
     }
     
  private:
     bool _conflictingSorts;
     QueryResType _arg;  
     VirtualIterator<CombSubstitution*> _csIt;
  };

private:
  Clause* performSuperposition(
	  Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
	  Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
	  ResultSubstitutionSP subst, bool eqIsResult, Limits* limits,
          UnificationConstraintStackSP constraints);
  
  /** Performs superposition with some ordering constraint absent. 
    * For example no check is carried out to ensure that in literals s = t
    * s > t. Its primary usage is when using combinatory unifcation where
    * standard superposition would result in inferences being lost unless
    * an ordering compatible with combinatory unification can be designed
    */
  Clause* performParamodulation(
	  Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
	  Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
	  ResultSubstitutionSP subst, bool eqIsResult, Limits* limits);
  
  bool checkClauseColorCompatibility(Clause* eqClause, Clause* rwClause);
  static int getWeightLimit(Clause* eqClause, Clause* rwClause, Limits* limits);
  static bool earlyWeightLimitCheck(Clause* eqClause, Literal* eqLit,
      Clause* rwClause, Literal* rwLit, TermList rwTerm, TermList eqLHS, TermList eqRHS,
      ResultSubstitutionSP subst, bool eqIsResult, int weightLimit);

  static bool checkSuperpositionFromVariable(Clause* eqClause, Literal* eqLit, TermList eqLHS);

  static size_t getSubtermOccurrenceCount(Term* trm, TermList subterm);
  
  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct ApplicableRewritesFn;

  struct LHSsFn;
  struct RewritableResultsFn;
  struct BackwardResultFn;

  struct ApplicableCombRewritesFn;
  
  SuperpositionSubtermIndex* _subtermIndex;
  SuperpositionLHSIndex* _lhsIndex;
};


};

#endif /* __Superposition__ */
