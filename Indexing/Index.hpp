/**
 * @file VirtualIterator.hpp
 * Defines abstract Index class and some other auxiliary classes.  
 */

#ifndef __Indexing_Index__
#define __Indexing_Index__

#include "../Forwards.hpp"

#include "../Kernel/MMSubstitution.hpp"
#include "../Lib/Event.hpp"
#include "../Lib/Exception.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Saturation/ClauseContainer.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Lib;
using namespace Saturation;

/**
 * Class of objects which contain results of single literal queries.
 */
struct SLQueryResult
{
  SLQueryResult(Literal* l, Clause* c, MMSubstitution* s)
  :literal(l), clause(c), substitution(s) {}

  SLQueryResult(Clause* c, MMSubstitution* s)
  :literal(0), clause(c), substitution(s) {}
  
  Literal* literal;
  Clause* clause;
  const MMSubstitution* substitution;
};


typedef VirtualIterator<SLQueryResult> SLQueryResultIterator;

class Index
{
public:
  virtual ~Index();
  virtual SLQueryResultIterator getComplementaryUnifications(Literal* lit)
  {
    INVALID_OPERATION("Operation not supported by this index.");
  }
  void attachContainer(ClauseContainer* cc);
  void detachContainer(ClauseContainer* cc);
  
protected:
  Index(): _attachedContainers(0) {}

  virtual void onAddedToContainer(Clause* c);
  virtual void onRemovedFromContainer(Clause* c);
  
  virtual void insert(Literal* lit, Clause* cls) = 0;
  virtual void remove(Literal* lit, Clause* cls) = 0;

  //TODO: postponing index modifications during iteration (methods isBeingIterated() etc...)
  
private:
  typedef List<ClauseContainer*> ContainerList;
  ContainerList* _attachedContainers;
};

};
#endif /*__Indexing_Index__*/
