/**
 * @file LiteralMiniIndex.hpp
 * Defines class LiteralMiniIndex.
 */


#ifndef __LiteralMiniIndex__
#define __LiteralMiniIndex__

#include "../Forwards.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;


class LiteralMiniIndex
{
public:
  LiteralMiniIndex(Clause* cl);
  ~LiteralMiniIndex();

private:
  struct Entry
  {
    Entry(unsigned header, Literal* lit) : header(header), lit(lit) {}
    unsigned header;
    Literal* lit;
  };
  unsigned _cnt;
  Entry* _entries;
public:
  struct InstanceIterator {
    InstanceIterator(LiteralMiniIndex& index, Literal* base);
    bool hasNext();
    Literal* next();
  private:
    Entry* _curr;
  };
};

};

#endif /* __LiteralMiniIndex__ */
