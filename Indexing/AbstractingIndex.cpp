/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "AbstractingIndex.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/TermIterators.hpp"

#define QUERY_BANK 0
#define RESULT_BANK 1

namespace Indexing {

struct AbstractingTransformer 
  : public TermTransformer 
{
  AbstractingIndex& index;
  TermList origTerm;
  Stack<AbstractingIndex::IntroducedSpecialVar> introducedVars;
  unsigned nextVar;

  AbstractingTransformer(AbstractingIndex& index, TermList origTerm) : index(index), introducedVars() 
  {
    unsigned max = 0;
    VariableIterator iter(origTerm);
    while (iter.hasNext()) {
      max = std::max(max, iter.next().var());
    }
    nextVar = max + 1;
  }

  TermList transformTermList(TermList t) 
  { return t.isVar() ? t : TermList(transform(t.term())); }

  virtual TermList transformSubterm(TermList trm) final override
  {
    auto transformOnce = [this](auto trm) {
      for (auto& a : *index._abstractors) {
        auto res = a.replaceAbstractableSubterm(trm, [&]() { return TermList::var(this->nextVar++); });
        if (res.isSome()) {
          introducedVars.push(AbstractingIndex::IntroducedSpecialVar {
              .var = res.unwrap().var,
              .origTerm = res.unwrap().varDefinition,
              .abstractor = &a,
              });
          ASS_NEQ(res.unwrap().transformed, trm);
          return res.unwrap().transformed;
        }
      }
      return trm;
    };
    TermList transformed = trm;
    do {
      trm = transformed;
      transformed = transformOnce(trm);
    } while (trm != transformed);

    return trm;
  }
};

AbstractingIndex::TransformedTerm const& AbstractingIndex::replaceAbstractableSubterms(TermList t) 
{
  auto e = _transformedTerms.findPtr(t);
  if (e) {
    e->second++;
    return e->first;

  } else {
    auto trafo = AbstractingTransformer(*this, t);
    auto res = trafo.transformTermList(t);

    auto entry = TransformedTerm {
        .term = res,
        .introducedVars = std::move(trafo.introducedVars)
    };
    _transformedTerms.insert(t, make_pair(std::move(entry), 1));
    _origTerms.insert(res, t);

    return _transformedTerms.get(t).first;
  }
}


void AbstractingIndex::insert(TermList t, Literal* lit, Clause* cls)
{ 
  CALL("AbstractingIndex::insert")
  _inner->insert(replaceAbstractableSubterms(t).term, lit, cls); 
}

void AbstractingIndex::remove(TermList t, Literal* lit, Clause* cls)
{ 
  CALL("AbstractingIndex::remove")
  auto& trafo = *_transformedTerms.findPtr(t);
  _inner->remove(trafo.first.term, lit, cls); 
  if (--trafo.second == 0) {
    ALWAYS(_origTerms.remove(trafo.first.term));
    ALWAYS(_transformedTerms.remove(t));
  }
}

template<class UnificationsFun>
TermQueryResultIterator AbstractingIndex::__getUnifications(TermList query, UnificationsFun unify) 
{
  auto& transformed = replaceAbstractableSubterms(query);
  auto& lvars = transformed.introducedVars;
  return pvi(iterTraits(unify(transformed.term))
    .filterMap([&lvars, this, query](TermQueryResult qr) {  
      auto& rvars = _transformedTerms.get(_origTerms.get(qr.term)).first.introducedVars;

      qr.constraints = decltype(qr.constraints)(new Stack<UnificationConstraint>());

      auto substitutionToConstraints = [&](auto origTerm, auto& vars, auto varBank) {
        auto sigma = [&](auto x) { return qr.substitution->apply(x, varBank); };

        for (auto introduced : vars) {

          if (!introduced.abstractor->canAbstract(sigma(introduced.origTerm), sigma(introduced.var))) 
            return false;

          qr.constraints->push(make_pair(
                make_pair(introduced.var     , varBank),
                make_pair(introduced.origTerm, varBank)));
        }
        return true;
      };

      auto validAbstraction 
        =  substitutionToConstraints(query,   lvars,  QUERY_BANK)
        && substitutionToConstraints(qr.term, rvars, RESULT_BANK);

      return validAbstraction ? Option<TermQueryResult>(std::move(qr))
                              : Option<TermQueryResult>();
     }));

}

TermQueryResultIterator AbstractingIndex::getUnifications(TermList query)
{
  return __getUnifications(query, 
      [&](auto transformed) { return _inner->getUnifications(transformed, /* retrieve substitutions */ true); });
}

TermQueryResultIterator AbstractingIndex::getUnificationsUsingSorts(TermList query, TermList sort)
{
  return __getUnifications(query, 
      [&](auto transformed) { return _inner->getUnificationsUsingSorts(transformed, sort, /* retrieve substitutions */ true); });
}

namespace Abstractors {

  bool isInterpreted(Term* t) 
  {
    return theory->isInterpretedFunction(t)
      || theory->isInterpretedConstant(t)
      || env.signature->getFunction(t->functor())->termAlgebraCons();
  }

  bool isInterpreted(TermList t) 
  { return t.isTerm() && isInterpreted(t.term()); }

  bool InterpretedOnly::canAbstract(TermList introduced, TermList unified) const
  {
    ASS(isInterpreted(introduced))
    return isInterpreted(unified);
  }

  template<class FreshVarFun>
  Option<VariableIntroductionResult> InterpretedOnly::replaceAbstractableSubterm(TermList toTransform, FreshVarFun freshVar) const
  {
    if (isInterpreted(toTransform)) {
      auto v = freshVar();
      return some(VariableIntroductionResult { .transformed = v, .var = v, .varDefinition = toTransform });
    } else {
      return none<VariableIntroductionResult>(); 
    }
  }


  bool OneSideInterpreted::canAbstract(TermList introduced, TermList unified) const
  {
    ASS(isInterpreted(introduced))
    return true;
  }

  template<class FreshVarFun>
  Option<VariableIntroductionResult> OneSideInterpreted::replaceAbstractableSubterm(TermList toTransform, FreshVarFun freshVar) const
  { return OneSideInterpreted::replaceAbstractableSubterm(toTransform, std::move(freshVar)); }


  bool FunctionExtensionality::canAbstract(TermList introduced, TermList unified) const
  {
    ASSERTION_VIOLATION_REP("TODO")
  }

  template<class FreshVarFun>
  Option<VariableIntroductionResult> FunctionExtensionality::replaceAbstractableSubterm(TermList toTransform, FreshVarFun freshVar) const
  { 
    ASSERTION_VIOLATION_REP("TODO") 
  }

} // namespace Abstractors

} // namespace Indexing

