/**
 * @file BinaryResolution.cpp
 * Implements class BinaryResolution for binary resolution
 * @since 05/01/2008 Torrevieja
 */

#include "../Lib/DArray.hpp"
#include "../Lib/Int.hpp"

#include "../Kernel/DoubleSubstitution.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"

#include "BinaryResolution.hpp"
#include "ProofAttempt.hpp"

// set this to 1 to trace all applications 
#define TRACE_RESOLUTION 0

#if TRACE_RESOLUTION
#include <fstream>
#include "../Test/Output.hpp"

static ofstream trace("resolution.log");
#endif

using namespace Kernel;
using namespace Resolution;

/**
 * Apply binary resolution to the @b _clause and all clauses in @b _pa;
 */
void BinaryResolution::apply()
{
  CALL("BinaryResolution::apply/0");

#if TRACE_RESOLUTION
  trace << "res1(" << Test::Output::toString(&_clause) << ").\n";
#endif

  for (int l = _clause.selected()-1;l >= 0;l--) {
    Literal* lit = _clause[l];
#if TRACE_RESOLUTION
    trace << "lit1(" << l << ").\n";
#endif
    if (lit->isEquality()) {
      continue;
    }
    apply(l,lit);
  }
} // BinaryResolution::apply

/**
 * Apply binary resolution to the @b _clause and all clauses in @b _pa
 * on a given literal.
 * @param lit the literal upon which resolution is applied
 * @param l the number of this literal in @b _clause
 */
void BinaryResolution::apply(int l,Literal* lit)
{
  CALL("BinaryResolution::apply/2");

  static DArray<Literal*> lits(64);
  static DoubleSubstitution subst;

  ClauseQueue::Iterator it(_pa.active());
  while (it.hasNext()) {
    Clause* d = it.next();
    if (d == &_clause) {
      continue;
    }
#if TRACE_RESOLUTION
    trace << "res2(" << Test::Output::toString(d) << ").\n";
#endif
    for (int j = d->selected()-1;j >= 0;j--) {
      Literal* dlit = (*d)[j];
#if TRACE_RESOLUTION
      trace << "lit2(" << j << ").\n";
#endif
      if (dlit->isEquality()) {
	continue;
      }
      subst.reset();
      if (subst.complementary(lit,0,dlit,1)) {
	int clength = _clause.length();
	int dlength = d->length();
	int m = clength+dlength-2;
	lits.ensure(m);
	// copy literals of d
	for (int i = dlength-1;i >= 0;i--) {
	  if (i == j) {
	    continue;
	  }
	  lits[--m] = subst.apply((*d)[i],1);
	}
	// copy literals of _clause
	for (int i = clength-1;i >= 0;i--) {
	  if (i == l) {
	    continue;
	  }
	  lits[--m] = subst.apply(_clause[i],0);
	}
	ASS(m == 0);
	// now lits contains the resulting clause of length clength+dlength-2f
	int newLength = clength+dlength-2;
	Clause* res = new(newLength)
                          Clause(newLength,
				 (Unit::InputType)Int::max(_clause.inputType(),
							   d->inputType()),
				 new Inference2(Inference::RESOLUTION,
						&_clause,
						d));
	int next = 0;
	for (int f = newLength-1;f >= 0;f--) {
	  if (lits[f]) {
	    (*res)[next++] = lits[f];
	  }
	}
	res->setAge(Int::max(_clause.age(),d->age())+1);
	_pa.unprocessed().insert(res);
#if TRACE_RESOLUTION
	trace << "resolvent(" << Test::Output::toString(res) << ").\n";
#endif
      }
//       cout << "C\n";
    }
  }
} // BinaryResolution::apply

