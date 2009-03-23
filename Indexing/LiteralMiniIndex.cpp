/**
 * @file LiteralMiniIndex.cpp
 * Implements class LiteralMiniIndex.
 */

#include <algorithm>
#include "../Lib/Allocator.hpp"

#include "LiteralMiniIndex.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;



LiteralMiniIndex::LiteralMiniIndex(Clause* cl)
: _cnt(cl->length())
{
  _entries=static_cast<Entry*>(ALLOC_KNOWN((_cnt+1)*sizeof(Entry), "LiteralMiniIndex"));
  for(unsigned i=0;i<_cnt;i++) {
    new(&_entries[i]) Entry((*cl)[i]->header(), (*cl)[i]);
  }

}

LiteralMiniIndex::~LiteralMiniIndex()
{
  DEALLOC_KNOWN(_entries, (_cnt+1)*sizeof(Entry), "LiteralMiniIndex");
}

}
