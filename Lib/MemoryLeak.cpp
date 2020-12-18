/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file MemoryLeak.cpp
 * Implements the class MemoryLeak used in debugging memory leaks.
 *
 * @since 22/03/2008 Torrevieja
 */


#if CHECK_LEAKS

#include "Hash.hpp"
#include "Stack.hpp"
#include "MemoryLeak.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"

using namespace Kernel;

bool MemoryLeak::_cancelled = false;

/**
 * Deallocate a formula @b f if the formula is not in the set @b s.
 * @since 22/03/2008 Torrevieja
 */
void MemoryLeak::release(Formula* f)
{
  CALL("MemoryLeak::release(Formula*)");

  if (_released.contains(f)) {
    return;
  }
  _released.insert(f);
  switch (f->connective()) {
  case LITERAL:
  case TRUE:
  case FALSE:
    break;
  case AND:
  case OR:
    {
      FormulaList* fs = f->args();
      while (fs) {
	if (_released.contains(fs)) {
	  break;
	}
	_released.insert(fs);
	FormulaList* next = fs->tail();
	release(fs->head());
	delete fs;
	fs = next;
      }
    }
    break;
  case IMP:
  case IFF:
  case XOR:
    release(f->left());
    release(f->right());
    break;
  case NOT:
    release(f->uarg());
    break;
  case FORALL:
  case EXISTS:
    {
      Formula::VarList* vs = f->vars();
      while (vs) {
	if (_released.contains(vs)) {
	  break;
	}
	_released.insert(vs);
	Formula::VarList* next = vs->tail();
	delete vs;
	vs = next;
      }
    }
    release(f->qarg());
    break;
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
  f->destroy();
} // MemoryLeak::release


/**
 * Deallocate a list of units.
 * @since 22/03/2008 Torrevieja
 */
void MemoryLeak::release(UnitList* units)
{
  Stack<Unit*> us(32);
  while (units) {
    UnitList* next = units->tail();
    Unit* u = units->head();
    if (_released.contains(u)) {
      continue;
    }
    _released.insert(u);
    us.push(u);
    delete units;
    units = next;
  }

  while (us.isNonEmpty()) {
    Unit* u = us.pop();
    Inference inf = u->inference();
    Inference::Iterator ps = inf.iterator();
    while (inf.hasNext(ps)) {
      Unit* p = inf.next(ps);
      if (_released.contains(p)) {
	continue;
      }
      _released.insert(p);
      us.push(p);
    }

    if (! u->isClause()) {
      release(static_cast<FormulaUnit*>(u)->formula());
      u->destroy();
    }
  }
} // MemoryLeak::release

#endif // CHECK_LEAKS
