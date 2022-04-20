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
 * @file LiteralMiniIndex.cpp
 * Implements class LiteralMiniIndex.
 */

#include <algorithm>
#include "Lib/Allocator.hpp"

#include "LiteralMiniIndex.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

/*int LiteralMiniIndex::goodPred=0;
int LiteralMiniIndex::badPred=0;*/


bool LiteralMiniIndex::literalHeaderComparator(const Entry& e1, const Entry& e2)
{
  return e1._header<e2._header || ( e1._header==e2._header && e1._weight<e2._weight );
}

LiteralMiniIndex::LiteralMiniIndex(Clause* cl)
: _cnt(cl->length()), _entries(cl->length()+1)
{
  init(cl->literals());
}

LiteralMiniIndex::LiteralMiniIndex(Literal* const * lits, unsigned length)
: _cnt(length), _entries(length+1)
{
  init(lits);
}

void LiteralMiniIndex::init(Literal* const * lits)
{
  ASS_G(_cnt, 0);
  bool hasAnsLit = false;
  unsigned ei = 0;
  for(unsigned i=0;i<_cnt;i++) {
    //// TODO(hzzv) new (if{}) for special terms:
    //if (lits[i]->isAnswerLiteral()) {
    //  hasAnsLit = true;
    //  continue;
    //}
    _entries[ei++].init(lits[i]);
  }
  //// TODO(hzzv) new for special terms:
  //_entries[hasAnsLit ? _cnt-1 : _cnt].initTerminal();
  //std::sort(_entries.begin(), _entries.end()-(hasAnsLit ? 2 : 1),literalHeaderComparator);
  // TODO(hzzv) old:
  _entries[_cnt].initTerminal();
  std::sort(_entries.begin(), _entries.end()-1,literalHeaderComparator);
}

}
