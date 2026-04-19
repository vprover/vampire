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
 * @file CodeTreeInterfaces.cpp
 * Implements indexing structures that use code trees.
 *
 */

#include "Indexing/Index.hpp"
#include "Inferences/ALASCA/Demodulation.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/Recycled.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Renaming.hpp"
#include "Kernel/Term.hpp"

#include "ClauseCodeTree.hpp"
#include "TermCodeTree.hpp"

#include "CodeTreeInterfaces.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

template<bool higherOrder, class Data>
class CodeTreeTIS<higherOrder, Data>::ResultIterator
: public IteratorCore<QueryRes<const GenSubstitution<Data>*, Data>>
{
public:
  ResultIterator(const CodeTreeTIS& tree, TypedTermList t, bool retrieveSubstitutions)
  : _retrieveSubstitutions(retrieveSubstitutions),
    _found(0), _finished(false), _tree(tree)
  {
    _matcher->init(&_tree._ct, t);

    if(_retrieveSubstitutions) {
      _subst = new GenSubstitution<Data>(&_matcher->bindings, &*_resultNormalizer);
    }
  }

  ~ResultIterator() override
  {
    if(_retrieveSubstitutions) {
      delete _subst;
    }
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

  QueryRes<const GenSubstitution<Data>*, Data> next() override
  {
    ASS(_found);

    if (_retrieveSubstitutions) {
      if constexpr (!is_indexed_data_normalized<Data>::value) {
        _resultNormalizer->reset();
        _resultNormalizer->normalizeVariables(_found->key());
      }
    }
    auto out = QueryRes<const GenSubstitution<Data>*, Data>(_subst, _found);
    _found=0;
    return out;
  }
private:
  GenSubstitution<Data>* _subst = nullptr;
  Recycled<Renaming> _resultNormalizer;
  bool _retrieveSubstitutions;
  Data* _found;
  bool _finished;
  const CodeTreeTIS& _tree;
  Recycled<typename TermCodeTree<higherOrder, Data>::TermMatcher> _matcher;
};

template<bool higherOrder, class Data>
VirtualIterator<QueryRes<const GenSubstitution<Data>*, Data>> CodeTreeTIS<higherOrder, Data>::getGeneralizations(TypedTermList t, bool retrieveSubstitutions) const
{
  if(_ct.isEmpty()) {
    return VirtualIterator<QueryRes<const GenSubstitution<Data>*, Data>>::getEmpty();
  }

  return vi( new ResultIterator(*this, t, retrieveSubstitutions) );
}

template class CodeTreeTIS<false, TermLiteralClause>;
template class CodeTreeTIS<true,  TermLiteralClause>;
template class CodeTreeTIS<false, DemodulatorData>;
template class CodeTreeTIS<true,  DemodulatorData>;
template class CodeTreeTIS<false, Inferences::ALASCA::Demodulation::Lhs>;
template class CodeTreeTIS<false, TermWithValue<TermList>>;

/////////////////   CodeTreeSubsumptionIndex   //////////////////////

template<bool higherOrder>
void CodeTreeSubsumptionIndex<higherOrder>::handleClause(Clause* cl, bool adding)
{
  TIME_TRACE("codetree subsumption index maintenance");

  if(adding) {
    _ct.insert(cl);
  }
  else {
    _ct.remove(cl);
  }
}

template class CodeTreeSubsumptionIndex<false>;
template class CodeTreeSubsumptionIndex<true>;

}
