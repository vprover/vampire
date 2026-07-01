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
 * @file CodeTreeInterfaces.hpp
 * Defines classes of indexing structures that use code trees.
 */

#ifndef __CodeTreeInterfaces__
#define __CodeTreeInterfaces__

#include "Forwards.hpp"

#include "TermCodeTree.hpp"
#include "ClauseCodeTree.hpp"

#include "Index.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Lib;

template<class Data>
class GenSubstitution
  : public SubstApplicator
{
public:
  GenSubstitution(CodeTree::BindingArray* bindings, Renaming* resultNormalizer)
  : _bindings(bindings), _resultNormalizer(resultNormalizer) {}

  USE_ALLOCATOR(GenSubstitution);

  TermList apply(unsigned var) const override {
    if constexpr (is_indexed_data_normalized<Data>::value) {
      return (*_bindings)[var];
    } else {
      ASS(_resultNormalizer->contains(var));
      unsigned nvar=_resultNormalizer->get(var);
      TermList res=(*_bindings)[nvar];
      ASS(res.isTerm()||res.isOrdinaryVar());
      ASSERT_VALID(res);
      return res;
    }
  }

  TermList apply(TermList t) const {
    return SubstHelper::apply(t, *this);
  }

  Literal* apply(Literal* lit) const {
    return SubstHelper::apply(lit, *this);
  }
private:
  CodeTree::BindingArray* _bindings;
  Renaming* _resultNormalizer;
};

/**
 * Term indexing structure using code trees to retrieve generalizations
 */
template<bool higherOrder, class Data>
class CodeTreeTIS
{
public:
  /* INFO: we ignore unifying the sort of the keys here */
  void handle(Data data, bool insert)
  {
    if (insert) {
      auto ti = new Data(std::move(data));
      _ct.insert(ti);
    } else {
      _ct.remove(data);
    }
  }

  VirtualIterator<QueryRes<const GenSubstitution<Data>*, Data>> getGeneralizations(TypedTermList t, bool retrieveSubstitutions = true) const;

  void output(std::ostream& out) const { out << _ct; }

private:
  class ResultIterator;

  TermCodeTree<higherOrder, Data> _ct;
};

template<bool higherOrder>
class CodeTreeSubsumptionIndex
: public Index
{
public:
  CodeTreeSubsumptionIndex(SaturationAlgorithm&) {}
  ClauseCodeTree<higherOrder>* getClauseCodeTree() { return &_ct; }
protected:
  void handleClause(Clause* c, bool adding) override;
private:

  ClauseCodeTree<higherOrder> _ct;
};

};
#endif /*__CodeTreeInterfaces__*/
