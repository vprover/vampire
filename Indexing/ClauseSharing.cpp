/**
 * @file ClauseSharing.cpp
 * Implements class ClauseSharing.
 */

#include "../Lib/Environment.hpp"

#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/InferenceStore.hpp"

#include "../Shell/Statistics.hpp"

#include "ClauseSharing.hpp"

namespace Indexing
{
using namespace Lib;
using namespace Kernel;

/**
 * If the sharing index contains a clause that is variant
 * of the literals in the @b lits array, return it.
 * Otherwise return 0.
 *
 * For variants we consider only the non-propositional parts 
 * of clauses.
 */
Clause* ClauseSharing::tryGet(Literal** lits, unsigned len)
{
  CALL("ClauseSharing::tryGet/2");

  ClauseIterator variants=_index.retrieveVariants(lits, len);
  if(!variants.hasNext()) {
    return false;
  }
  Clause* res=variants.next();
  ASS(!variants.hasNext());
  return res;
}

/** 
 * Return a variant of the clause @b c if it is contained in 
 * the sharing index, otherwise return 0
 *
 * For variants we consider only the non-propositional parts 
 * of clauses.
 */
Clause* ClauseSharing::tryGet(Clause* c)
{
  CALL("ClauseSharing::tryGet/1");

  return tryGet(c->literals(), c->length());
}

/**
 * Insert a clause @b c that is new (it does not have 
 * a variant in the index)
 *
 * For variants we consider only the non-propositional parts 
 * of clauses.
 */
void ClauseSharing::insertNew(Clause* c)
{
  CALL("ClauseSharing::insertNew");
  ASS_EQ(tryGet(c),0); //the clause is really new

  env.statistics->uniqueComponents++;

  c->incRefCnt();
  {
    TimeCounter tc(TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE);
    _index.insert(c);
  }
}

/**
 * If a variant of the clause @b cl is already present in the 
 * sharing index, merge their propositional parts. Otherwise
 * insert @b cl into the index. Assign the information about
 * what has happened into @b res and return the clause that is
 * in the index.
 *
 * For variants we consider only the non-propositional parts 
 * of clauses.
 */
Clause* ClauseSharing::insert(Clause* cl, InsertionResult& res)
{
  CALL("ClauseSharing::insert");

  ClauseIterator variants=_index.retrieveVariants(cl->literals(), cl->length());
  if(variants.hasNext()) {
    Clause* comp=variants.next();

    ASS(!variants.hasNext());

    BDDNode* oldCompProp=comp->prop();
    BDDNode* oldClProp=cl->prop();
    BDDNode* newCompProp=BDD::instance()->conjunction(oldCompProp, oldClProp);

    if(oldCompProp==newCompProp) {
      res=OLD;
      return comp;
    }

    comp->setProp( newCompProp );
    InferenceStore::instance()->recordMerge(comp, oldCompProp, cl, newCompProp);

    res=OLD_MODIFIED;
    return comp;

  } else {
    insertNew(cl);

    res=INSERTED;
    return cl;
  }

}

}
