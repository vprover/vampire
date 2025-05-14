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
 * @file LiteralMiniIndex.hpp
 * Defines class LiteralMiniIndex.
 */


#ifndef __LiteralMiniIndex__
#define __LiteralMiniIndex__

#include "Forwards.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Matcher.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;


class LiteralMiniIndex
{
public:
  USE_ALLOCATOR(LiteralMiniIndex);

  LiteralMiniIndex() = default;
  void init(Clause* cl);

  LiteralMiniIndex(Clause* cl);
  LiteralMiniIndex(Literal* const * lits, unsigned length);

private:
  void init(Literal* const * lits);

  friend std::ostream& operator<<(std::ostream& out, LiteralMiniIndex const& idx)
  {  return out << "[" << Output::interleaved(", ", arrayIter(idx._entries, idx._cnt).map([](auto& e) -> Literal& { return *e._lit; }))<< "]"; }

  struct Entry
  {
    Entry() {}
    void initTerminal() { _header=0xFFFFFFFF; _lit=0; }
    void init(Literal* lit) { _header=lit->header(); _weight=lit->weight(); _lit=lit; }
    unsigned _header;
    unsigned _weight;
    Literal* _lit;
  };

  static bool literalHeaderComparator(const Entry& e1, const Entry& e2);

  unsigned _cnt = 0;
  DArray<Entry> _entries;

  struct IteratorBase
  {
    IteratorBase(LiteralMiniIndex const& index, Literal* query, bool complementary)
    : _ready(false), _hdr(complementary?query->complementaryHeader():query->header()),
    _query(query), _compl(complementary)
    {
      Entry const* arr=index._entries.array();
      unsigned weight=query->weight();
      if(arr[0]._header>=_hdr || index._cnt==1) {
	_curr=arr;
	return;
      }
      unsigned left=1;
      unsigned right=index._cnt-1;
      while(left<right) {
	unsigned mid=(left+right)/2;
	if(arr[mid]._header<_hdr || (arr[mid]._header==_hdr && arr[mid]._weight<weight)) {
	  left=mid+1;
	} else {
	  right=mid;
	}
      }
      ASS_EQ(left,right);
      _curr=&arr[right];
      ASS(_curr->_header==_hdr ||
	      (_curr->_header<_hdr && (_curr+1)->_header>_hdr) ||
	      (_curr->_header>_hdr && (_curr==arr || (_curr-1)->_header<_hdr || (_curr-1)->_weight<weight)) );
    }
    Literal* next()
    {
      ASS(_ready);
      _ready=false;
      return (_curr++)->_lit;
    }

    bool _ready;
    unsigned _hdr;
    Literal* _query;
    bool _compl;
    Entry const* _curr;
  };

public:

  // Returns all literals in the given mini-index that are an instance of the given base literal.
  struct InstanceIterator
      : IteratorBase {
    InstanceIterator(LiteralMiniIndex const& index, Literal* base, bool complementary)
        : IteratorBase(index, base, complementary)
    {
    }

    bool hasNext()
    {
      if(_ready) { return true; }
      while(_curr->_header==_hdr) {
        if(MatchingUtils::match(_query, _curr->_lit, _compl)) {
          _ready=true;
          return true;
        }
        _curr++;
      }
      return false;
    }

    // Same as hasNext(), but allows using a custom binder for matching:
    // - see comments on MatchingUtils::match for information about binders
    // - this can be used to extract variable bindings with the match
    template <class Binder>
    bool hasNext(Binder& binder)
    {
      if (_ready) {
        return true;
      }
      while (_curr->_header == _hdr) {
        if (MatchingUtils::match(_query, _curr->_lit, _compl, binder)) {
          _ready = true;
          return true;
        }
        _curr++;
      }
      return false;
    }

    Literal* next()
    {
      return IteratorBase::next();
    }
  };

  // Returns all literals in the given mini-index that are a variant of the given base literal.
  struct VariantIterator
  : IteratorBase
  {
    VariantIterator(LiteralMiniIndex& index, Literal* query, bool complementary)
    : IteratorBase(index, query, complementary)
    {}

    bool hasNext()
    {
      if(_ready) { return true; }
      while(_curr->_header==_hdr) {
	if(MatchingUtils::isVariant(_query, _curr->_lit)) {
	  _ready=true;
	  return true;
	}
	_curr++;
      }
      return false;
    }
    Literal* next()
    {
      return IteratorBase::next();
    }
  };
};

};

#endif /* __LiteralMiniIndex__ */
