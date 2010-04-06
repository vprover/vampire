/**
 * @file TermCodeTree.hpp
 * Defines class TermCodeTree.
 */

#ifndef __TermCodeTree__
#define __TermCodeTree__

#include "../Forwards.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Recycler.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/TriangularArray.hpp"
#include "../Lib/Vector.hpp"
#include "../Lib/VirtualIterator.hpp"


#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

class TermCodeTree : public CodeTree 
{
public:
  struct TermInfo
  {
    TermInfo(TermList t, Literal* lit, Clause* cls)
    : t(t), lit(lit), cls(cls) {}

    inline bool operator==(const TermInfo& o)
    { return cls==o.cls && t==o.t && lit==o.lit; }

    inline bool operator!=(const TermInfo& o)
    { return !(*this==o); }

    CLASS_NAME("TermCodeTree::TermInfo");
    USE_ALLOCATOR(TermInfo);

    TermList t;
    Literal* lit;
    Clause* cls;
  };

public:
  void insert(TermInfo* ti);
  void remove(const TermInfo& ti);
  
public:
  struct TermMatcher
  : public Matcher
  {
    void init(CodeTree* tree, TermList t);
    void deinit();
    
    TermInfo* next();
    
    CLASS_NAME("TermCodeTree::TermMatcher");
    USE_ALLOCATOR(TermMatcher);
  };

};

};

#endif // __TermCodeTree__
