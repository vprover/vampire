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
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Renaming.hpp"

#include "LiteralCodeTree.hpp"
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
  GenSubstitution(const CodeTree::BindingArray& bindings, const Renaming& resultNormalizer)
  : _bindings(bindings), _resultNormalizer(resultNormalizer) {}

  TermList apply(unsigned var) const override {
    if constexpr (!is_indexed_data_normalized<Data>::value) {
      ASS(_resultNormalizer.contains(var));
      var = _resultNormalizer.get(var);
    }
    return _bindings[var];
  }

  template<typename Val> Val apply(Val v) const
  { return SubstHelper::apply(v, *this); }

private:
  const CodeTree::BindingArray& _bindings;
  const Renaming& _resultNormalizer;
};

template<typename Data>
using GenSubstitutionQR = QueryRes<const GenSubstitution<Data>&, Data>;

template<typename Data, typename Matcher>
class ResultIterator
  : public IteratorCore<GenSubstitutionQR<Data>>
{
public:
  template<typename ...Args>
  ResultIterator(const CodeTree& tree, Args... args)
  : _subst(_matcher->bindings, *_resultNormalizer)
  {
    _matcher->init(tree, args...);
  }

  USE_ALLOCATOR(ResultIterator);

  bool hasNext() override
  {
    if(_found) {
      return true;
    }
    if(_finished) {
      return false;
    }
    _found = _matcher->next();
    if(!_found) {
      _finished=true;
    }
    return _found;
  }

  GenSubstitutionQR<Data> next() override
  {
    ASS(_found);
    if constexpr (!is_indexed_data_normalized<Data>::value) {
      _resultNormalizer->reset();
      _resultNormalizer->normalizeVariables(_found->key());
    }
    auto out = GenSubstitutionQR<Data>(_subst, _found);
    _found = nullptr;
    return out;
  }
private:
  Recycled<Renaming> _resultNormalizer;
  Data* _found = nullptr;
  bool _finished = false;
  Recycled<Matcher> _matcher;
  GenSubstitution<Data> _subst;
};

/**
 * Term indexing structure using code trees to retrieve generalizations
 */
template<class Data>
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

  auto getGeneralizations(TypedTermList t) const {
    if(_ct.isEmpty()) {
      return VirtualIterator<GenSubstitutionQR<Data>>::getEmpty();
    }

    return vi( new ResultIterator<Data, typename TermCodeTree<Data>::TermMatcher>(_ct, t) );
  }

private:
  TermCodeTree<Data> _ct;
};

/**
 * Literal indexing structure using code trees to retrieve generalizations
 */
template<class Data>
class CodeTreeLIS
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

  auto getGeneralizations(Literal* lit, bool complementary) const
  {
    if(_ct.isEmpty()) {
      return VirtualIterator<GenSubstitutionQR<Data>>::getEmpty();
    }
    return vi( new ResultIterator<Data, typename LiteralCodeTree<Data>::LiteralMatcher>(_ct, lit, complementary) );
  }

  friend std::ostream& operator<<(std::ostream& out, Output::Multiline<CodeTreeLIS<Data>> const& self)
  { return out << self.self._ct; }

private:
  LiteralCodeTree<Data> _ct;
};

class CodeTreeSubsumptionIndex
: public Index
{
public:
  CodeTreeSubsumptionIndex(SaturationAlgorithm&) {}
  ClauseCodeTree* getClauseCodeTree() { return &_ct; }
protected:
  void handleClause(Clause* c, bool adding) override {
    // Insertion and removal are nothing alike -- insertion compiles a clause and merges
    // the code into the tree, removal runs the matching interpreter to find the clause's
    // path and then performs surgery -- so they get a node each. The outer node stays,
    // rather than the two replacing it: a sweep's node whitelist is derived from this
    // source tree, so a *renamed* node makes every earlier sweep unreadable, and the
    // rule that keeps that from ever mattering is to add children and never rename.
    // It costs one extra scope per call, ~0.01% of a sweep, which is worth not having
    // to keep a list of retired names correct forever.
    TIME_TRACE("codetree subsumption index maintenance");

    if(adding) {
      TIME_TRACE("codetree subsumption index insert");
      _ct.insert(c);
    }
    else {
      TIME_TRACE("codetree subsumption index remove");
      _ct.remove(c);
    }
  }
private:
  ClauseCodeTree _ct;
};

};
#endif /*__CodeTreeInterfaces__*/
