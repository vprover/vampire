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
  SLQueryResult() {}
  SLQueryResult(Literal* l, Clause* c, MMSubstitution* s)
  :literal(l), clause(c), substitution(s) {}

  SLQueryResult(Clause* c, MMSubstitution* s)
  :literal(0), clause(c), substitution(s) {}

  Literal* literal;
  Clause* clause;
  const MMSubstitution* substitution;
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
  const MMSubstitution* substitution;
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

  virtual void onAddedToContainer(Clause* c) {}
  virtual void onRemovedFromContainer(Clause* c) {}

  //TODO: postponing index modifications during iteration (methods isBeingIterated() etc...)

private:
  typedef List<ClauseContainer*> ContainerList;
  typedef List<SubscriptionData> SDataList;
  ContainerList* _attachedContainers;
  SDataList* _subscriptionData;
};

class LiteralIndex
: public Index
{
public:
  virtual ~LiteralIndex();

  SLQueryResultIterator getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true);

  SLQueryResultIterator getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true);

  SLQueryResultIterator getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true);

protected:
  LiteralIndex(LiteralIndexingStructure* is) : _is(is) {}

  LiteralIndexingStructure* _is;
};

class GeneratingLiteralIndex
: public LiteralIndex
{
public:
  GeneratingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void onAddedToContainer(Clause* c);
  void onRemovedFromContainer(Clause* c);
};

class SimplifyingLiteralIndex
: public LiteralIndex
{
public:
  SimplifyingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void onAddedToContainer(Clause* c);
  void onRemovedFromContainer(Clause* c);
};

class AtomicClauseSimplifyingLiteralIndex
: public LiteralIndex
{
public:
  AtomicClauseSimplifyingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void onAddedToContainer(Clause* c);
  void onRemovedFromContainer(Clause* c);
};



};
#endif /*__Indexing_Index__*/
