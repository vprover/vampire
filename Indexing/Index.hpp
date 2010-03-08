/**
 * @file Indexing/Index.hpp
 * Defines abstract Index class and some other auxiliary classes.
 */

#ifndef __Indexing_Index__
#define __Indexing_Index__

#include "../Forwards.hpp"

#include "../Lib/Event.hpp"
#include "../Lib/Exception.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Saturation/ClauseContainer.hpp"
#include "ResultSubstitution.hpp"

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
  SLQueryResult(Literal* l, Clause* c, ResultSubstitutionSP s)
  :literal(l), clause(c), substitution(s) {}
  SLQueryResult(Literal* l, Clause* c)
  :literal(l), clause(c) {}


  Literal* literal;
  Clause* clause;
  ResultSubstitutionSP substitution;

  struct ClauseExtractFn
  {
    DECL_RETURN_TYPE(Clause*);
    Clause* operator()(const SLQueryResult& res)
    {
      return res.clause;
    }
  };
};

/**
 * Class of objects which contain results of term queries.
 */
struct TermQueryResult
{
  TermQueryResult() {}
  TermQueryResult(TermList t, Literal* l, Clause* c, ResultSubstitutionSP s)
  :term(t), literal(l), clause(c), substitution(s) {}
  TermQueryResult(TermList t, Literal* l, Clause* c)
  :term(t), literal(l), clause(c) {}

  TermList term;
  Literal* literal;
  Clause* clause;
  ResultSubstitutionSP substitution;
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
