/**
 * @file LiteralMiniIndex.hpp
 * Defines class LiteralMiniIndex.
 */


#ifndef __LiteralMiniIndex__
#define __LiteralMiniIndex__

#include "../Forwards.hpp"
#include "../Lib/DArray.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Matcher.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;


class LiteralMiniIndex
{
public:
  LiteralMiniIndex(Clause* cl);

private:
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

  unsigned _cnt;
  DArray<Entry> _entries;
public:

  /*static int goodPred;
  static int badPred;*/

  struct InstanceIterator {
    InstanceIterator(LiteralMiniIndex& index, Literal* base, bool complementary)
    : _ready(false), _hdr(complementary?base->complementaryHeader():base->header()),
    _base(base), _compl(complementary)
    {
      CALL("LiteralMiniIndex::InstanceIterator::InstanceIterator");

      Entry* arr=index._entries.array();
      unsigned weight=base->weight();
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
    bool hasNext()
    {
      CALL("LiteralMiniIndex::InstanceIterator::hasNext");

      if(_ready) { return true; }
      while(_curr->_header==_hdr) {
	bool prediction=_curr->_lit->couldArgsBeInstanceOf(_base);
#if VDEBUG
	if(MatchingUtils::match(_base, _curr->_lit, _compl)) {
	  ASS(prediction);
#else
	if(prediction && MatchingUtils::match(_base, _curr->_lit, _compl)) {
#endif
	  _ready=true;
	  return true;
	}

	_curr++;
      }
      return false;
    }
    Literal* next()
    {
      ASS(_ready);
      _ready=false;
      return (_curr++)->_lit;
    }
  private:
    bool _ready;
    unsigned _hdr;
    Literal* _base;
    bool _compl;
    Entry* _curr;
  };
};

};

#endif /* __LiteralMiniIndex__ */
