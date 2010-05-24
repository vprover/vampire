/**
 * @file ClauseSharing.cpp
 * Implements class ClauseSharing.
 */

#include "Lib/Environment.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "ClauseSharing.hpp"

namespace Indexing
{
using namespace Lib;
using namespace Kernel;
using namespace Saturation;

void ClauseSharing::init(SaturationAlgorithm* sa)
{
  CALL("ClauseSharing::init");

  _sa=sa;
}

/**
 * Make the clause @b cl shared, and return true if the clause
 * should be retained (otherwise its variant is already in the
 * sharing index)
 */
bool ClauseSharing::doSharing(Clause* cl)
{
  CALL("ClauseSharing::doSharing");

  ClauseSharing::InsertionResult res;
  Clause* shCl=insert(cl, res);

  if(cl!=shCl) {
    if(res==ClauseSharing::OLD_MODIFIED) {
      _sa->addNewClause(shCl);
    }
    _sa->onParenthood(shCl, cl);
    if(res==ClauseSharing::OLD) {
	if(shCl->store()==Clause::ACTIVE || shCl->store()==Clause::PASSIVE ||
	    shCl->store()==Clause::REACTIVATED || shCl->store()==Clause::SELECTED_REACTIVATED) {
	  _sa->onNonRedundantClause(shCl);
	}
    }
    ASS(res==ClauseSharing::OLD || res==ClauseSharing::OLD_MODIFIED);
    return true;
  }
  ASS(res==ClauseSharing::INSERTED || res==ClauseSharing::ALREADY_THERE);
  return false;

}

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

    if(comp==cl) {
      res=ALREADY_THERE;
      return cl;
    }

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
