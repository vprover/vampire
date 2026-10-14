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
 * @file TermIndex.hpp
 * Defines class TermIndex.
 */


#ifndef __TermIndex__
#define __TermIndex__

#include "Index.hpp"
#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

namespace Indexing {

template<class Data>
class TermIndex
: public Index
{
public:
  template<bool higherOrder>
  VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(TypedTermList t, const Options& opt)
  {
    auto uwa = opt.unificationWithAbstraction();
    auto fpi = opt.unificationWithAbstractionFixedPointIteration();
    if constexpr (higherOrder) {
      return _is.getUwaHOL(t, uwa, fpi, opt.higherOrderUnifDepth(), opt.functionExtensionality()==Options::FunctionExtensionality::ABSTRACTION);
    } else {
      return _is.getUwa(t, uwa, fpi, /*funcExt=*/false);
    }
  }

  VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getUnifications(TypedTermList t, bool retrieveSubstitutions = true)
  { return _is.getUnifications(t, retrieveSubstitutions); }

  template<bool higherOrder>
  VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getInstances(TypedTermList t, bool retrieveSubstitutions = true)
  {
    if constexpr (higherOrder) {
      // TODO(HOL): implement proper higher-order matching here
      // we override retrieveSubstitutions because we need the substitution for the aftercheck
      return pvi(iterTraits(_is.getInstances(t, /*retrieveSubstitutions=*/true))
        .filter([t](auto qr) {
          return iterTraits(VariableIterator(t)).all([&qr](TermList var) {
            return !qr.unifier->applyToBoundQuery(var).containsLooseDBIndex();
          });
        }));
    } else {
      return _is.getInstances(t, retrieveSubstitutions);
    }
  }

  friend std::ostream& operator<<(std::ostream& out, TermIndex const& self)
  { return out << *self._is; }
protected:
  TermSubstitutionTree<Data> _is;
};

template<class Data>
class GeneralizingTermIndex
: public Index
{
public:
  auto getGeneralizations(TypedTermList t) const
  { return iterTraits(_ct.getGeneralizations(t)); }

  friend std::ostream& operator<<(std::ostream& out, GeneralizingTermIndex const& self)
  { return out << self._ct; }
protected:
  CodeTreeTIS<Data> _ct;
};

template<bool higherOrder>
class SuperpositionSubtermIndex
: public TermIndex<TermLiteralClause>
{
public:
  SuperpositionSubtermIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const Ordering& _ord;
};

class SuperpositionLHSIndex
: public TermIndex<TermLiteralClause>
{
public:
  SuperpositionLHSIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const Ordering& _ord;
  const Options& _opt;
};

/**
 * Term index for induction
 */
class InductionTermIndex
: public TermIndex<TermLiteralClause>
{
public:
  InductionTermIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const bool _inductionGroundOnly;
};

/**
 * Term index for structural induction
 */
class StructInductionTermIndex
: public GeneralizingTermIndex<TermLiteralClause>
{
public:
  StructInductionTermIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const bool _inductionGroundOnly;
};

} // namespace Indexing
#endif /* __TermIndex__ */
