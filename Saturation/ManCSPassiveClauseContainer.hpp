#ifndef __MANCSPASSIVECLAUSECONTAINER__
#define __MANCSPASSIVECLAUSECONTAINER__

#include <vector>
#include "Kernel/Clause.hpp"
#include "ClauseContainer.hpp"
#include "Kernel/ClauseQueue.hpp"

namespace Saturation {

using namespace Kernel;

/*
 * Subclass of PassiveClauseContainer for manual selection of clauses
 * asks in each iteration the user to pick the id of the clause which should be activated next
 */
class ManCSPassiveClauseContainer : public PassiveClauseContainer
{
public:
  CLASS_NAME(ManCSPassiveClauseContainer);
  USE_ALLOCATOR(ManCSPassiveClauseContainer);

  ManCSPassiveClauseContainer(const Options& opt) : opt(opt), clauses() {}
  virtual ~ManCSPassiveClauseContainer(){}
  
  virtual unsigned size() const;
  bool isEmpty() const;
  ClauseIterator iterator();

  void add(Clause* cl);
  void remove(Clause* cl);

  Clause* popSelected();
  
private:
  std::vector<Clause*> clauses;
  const Options& opt;
};

}

#endif /* __MANCSPASSIVECLAUSECONTAINER__ */