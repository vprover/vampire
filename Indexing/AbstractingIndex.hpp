/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Index.hpp"
#include "Lib/Option.hpp"
#include "Indexing/TermIndexingStructure.hpp"
#include "Lib/Map.hpp"
#include "Lib/Coproduct.hpp"



namespace Indexing {

namespace Abstractors {

  struct VariableIntroductionResult {
    TermList transformed;
    TermList var;
    TermList varDefinition;
  };


  ////////////////////////////////////////////////////////////////////////////////////
  // begin of UWA implemenatations
  //////////////////////////////////

  /** 
   * Each abstractor class defines a strategy how to perform unification with abstraction.
   *
   * In order to make use of UWA in an index we proceed as follows:
   * Insertion:
   * - we identify all positions in a term t where UWA could potentially be used
   * - we replace the subterms t' at all these positions by fresh variables v to get a term t*
   * - we insert t' into the index
   *
   * Lookup:
   * - we transform the term s to lookup to s* as for insertion
   * - we find all terms t*, and sigma that unify with s*
   * - for each t' (resp. s') we removed from t (resp. s) the original subterm we check whether sigma(v), t' is a valid abstraction point. if so we introduce a constraint 
   * - we return t, sigma, and all the constraints
   *
   * the function that identifies the points to perform abstraction at is `replaceAbstractableSubterm`. This function is called from within a top-down evaluation, hence has to only introduce on variable at a time, and will be fixed-point iterated
   * the function that checks whether the actual constraint introduction should be performed is canAbstract. One can assume that the first argument to that function is a term that has been replaced using `replaceAbstractableSubterm`
   */ 
  struct InterpretedOnly {
    bool canAbstract(TermList introduced, TermList unified) const;
    template<class FreshVarFun>
    Option<VariableIntroductionResult> replaceAbstractableSubterm(TermList toTransform, FreshVarFun freshVar) const;
  };

  struct OneSideInterpreted {
    bool canAbstract(TermList introduced, TermList unified) const;
    template<class FreshVarFun>
    Option<VariableIntroductionResult> replaceAbstractableSubterm(TermList toTransform, FreshVarFun freshVar) const;
  };

  struct FunctionExtensionality {
    bool canAbstract(TermList introduced, TermList unified) const;
    template<class FreshVarFun>
    Option<VariableIntroductionResult> replaceAbstractableSubterm(TermList toTransform, FreshVarFun freshVar) const;
  };


  ////////////////////////////////////////////////////////////////////////////////////
  // end of UWA implemenatations
  //////////////////////////////////

  using AnyAbstractor = Coproduct< InterpretedOnly 
                                 , OneSideInterpreted
                                 , FunctionExtensionality
                                 >;
}

struct Abstractor : Abstractors::AnyAbstractor {
  template<class AnyAbstractor> 
  Abstractor(AnyAbstractor a) : Abstractors::AnyAbstractor(std::move(a)) {}

  bool canAbstract(TermList introduced, TermList unified) const
  { return this->apply([&](auto& self) { return self.canAbstract(introduced, unified); }); }

  template<class FreshVarFun>
  Option<Abstractors::VariableIntroductionResult> replaceAbstractableSubterm(TermList toTransform, FreshVarFun freshVar) const
  { return this->apply([&](auto& self) { return self.replaceAbstractableSubterm(toTransform, std::move(freshVar)); }); }
};


class AbstractingIndex
: public Index
{
  shared_ptr<Stack<Abstractor>> _abstractors;
  TermIndexingStructure* _inner;

  struct IntroducedSpecialVar { 
    TermList var; 
    TermList origTerm; 
    Abstractor* abstractor;
  };

  struct TransformedTerm {
    TermList term;
    Stack<IntroducedSpecialVar> introducedVars;
  };

public:
  AbstractingIndex(shared_ptr<Stack<Abstractor>> abstractors, TermIndexingStructure* tis)
    : _abstractors(std::move(abstractors))
    , _inner(tis) 
  {  }

  void insert(TermList t, Literal* lit, Clause* cls);
  void remove(TermList t, Literal* lit, Clause* cls);

  TermQueryResultIterator getUnifications(TermList t);
  TermQueryResultIterator getUnificationsUsingSorts(TermList t, TermList sort);

private:
  template<class UnificationsFun>
  TermQueryResultIterator __getUnifications(TermList t, UnificationsFun unify);
  TransformedTerm const& replaceAbstractableSubterms(TermList);

  // maps terms to their transformed form
  // additionally there is a counter associated with each transformed term counting the number of times it has been inserted (potentially with different leafdata)
  DHMap<TermList, pair<TransformedTerm, unsigned>> _transformedTerms;
  // maps transformed terms to their original
  DHMap<TermList, TermList> _origTerms;
  friend struct AbstractingTransformer;
};

} // namespace Indexing
