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

/** Bank of the query term in substitution returned in SLQueryResult
 * and TermQueryResult objects.*/
#define QRS_QUERY_BANK 0
/** Bank of the retrieved term in substitution returned in SLQueryResult
 * and TermQueryResult objects.*/
#define QRS_RESULT_BANK 1

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
  SLQueryResult() {}
  SLQueryResult(Literal* l, Clause* c, MMSubstitution* s)
  :literal(l), clause(c), substitution(s) {}

  SLQueryResult(Clause* c, MMSubstitution* s)
  :literal(0), clause(c), substitution(s) {}

  Literal* literal;
  Clause* clause;
  MMSubstitution* substitution;
};

/**
 * Class of objects which contain results of term queries.
 */
struct TermQueryResult
{
  TermQueryResult() {}
  TermQueryResult(TermList t, Literal* l, Clause* c, MMSubstitution* s)
  :term(t), literal(l), clause(c), substitution(s) {}

  TermList term;
  Literal* literal;
  Clause* clause;
  MMSubstitution* substitution;
};

typedef VirtualIterator<SLQueryResult> SLQueryResultIterator;
typedef VirtualIterator<TermQueryResult> TermQueryResultIterator;

class Index
{
public:
  virtual ~Index();

  void attachContainer(ClauseContainer* cc);
  void detachContainer(ClauseContainer* cc);
protected:
  Index(): _attachedContainers(0), _subscriptionData(0) {}

  void onAddedToContainer(Clause* c)
  { handleClause(c, true); }
  void onRemovedFromContainer(Clause* c)
  { handleClause(c, false); }

  virtual void handleClause(Clause* c, bool adding) {}

  //TODO: postponing index modifications during iteration (methods isBeingIterated() etc...)

private:
  typedef List<ClauseContainer*> ContainerList;
  typedef List<SubscriptionData> SDataList;
  ContainerList* _attachedContainers;
  SDataList* _subscriptionData;
};



};
#endif /*__Indexing_Index__*/
