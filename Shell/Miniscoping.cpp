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
 * @file Miniscoping.cpp
 * Implementing the miniscoping transformation.
 */

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"

#include "Shell/Options.hpp"

#include "Miniscoping.hpp"

namespace Shell
{

/**
 * Miniscope the unit.
 *
 * @warning the unit must contain a rectified, NNF, flattened formula
 */
FormulaUnit* Miniscoping::miniscope(FormulaUnit* unit, Mode mode)
{
  ASS(! unit->isClause());

  Formula* f = unit->formula();
  Formula* g = miniscope(f, mode);
  if (f == g) { // not changed
    return unit;
  }

  FormulaUnit* res = new FormulaUnit(g,
      FormulaClauseTransformation(InferenceRule::MINISCOPE,unit));
  if (env.options->showPreprocessing()) {
    std::cout << "[PP] miniscoping in: " << unit->toString() << std::endl;
    std::cout << "[PP] miniscoping out: " << res->toString() << std::endl;
  }
  return res;
} // Miniscoping::miniscope

namespace {
/** The set @c s without the variable @c x. */
VarSet* minusVar(VarSet* s, unsigned x)
{
  return s->subtract(VarSet::getSingleton(x));
}
}

/**
 * Compute (and memoize in _fv) the free variables of every node of @c f,
 * in a single bottom-up pass; the analogue of Skolem::preskolemise.
 * Along the way, keep _nextVar above every variable index seen
 * (free at the leaves, or bound at the quantifier nodes).
 *
 * Also used to analyse the fresh copies made by rename() during pushing;
 * the memoization makes revisiting their unchanged shared subformulas free.
 */
VarSet* Miniscoping::computeFV(Formula* f)
{
  VarSet* res;
  if (_fv.find(f, res)) {
    return res;
  }

  switch (f->connective()) {
  case TRUE:
  case FALSE:
    res = VarSet::getEmpty();
    break;

  case LITERAL:
  case BOOL_TERM:
    {
      Stack<unsigned> vars(4);
      FormulaVarIterator fvi(f);
      while (fvi.hasNext()) {
        unsigned v = fvi.next();
        if (v >= _nextVar) { _nextVar = v+1; }
        vars.push(v);
      }
      res = VarSet::getFromIterator(Stack<unsigned>::Iterator(vars));
      break;
    }

  // apply() keeps these opaque, but they can still be queried as juncts
  case NOT:
    res = computeFV(f->uarg());
    break;
  case IMP:
  case IFF:
  case XOR:
    res = computeFV(f->left())->getUnion(computeFV(f->right()));
    break;

  case AND:
  case OR:
    {
      res = VarSet::getEmpty();
      FormulaList::Iterator it(f->args());
      while (it.hasNext()) {
        res = res->getUnion(computeFV(it.next()));
      }
      break;
    }

  case FORALL:
  case EXISTS:
    {
      VarSet* inner = computeFV(f->qarg());
      Stack<unsigned> bound(4);
      VSList::Iterator vit(f->vars());
      while (vit.hasNext()) {
        unsigned v = vit.next().first;
        if (v >= _nextVar) { _nextVar = v+1; }
        bound.push(v);
      }
      res = inner->subtract(VarSet::getFromIterator(Stack<unsigned>::Iterator(bound)));
      break;
    }

  case NAME:
  case NOCONN:
    ASSERTION_VIOLATION;
  }

  ALWAYS(_fv.insert(f, res));
  return res;
} // Miniscoping::computeFV

namespace {
/** An applicator for SubstHelper renaming a single variable. */
struct SingleVarRenaming
{
  unsigned from;
  TermList to;
  TermList apply(unsigned var) const
  { return var == from ? to : TermList::var(var); }
};
}

/**
 * Rename the free variable @c from to @c to in @c f.
 * Sound on rectified formulas: nothing inside @c f rebinds @c from,
 * and the fresh @c to cannot get captured.
 */
Formula* Miniscoping::rename(Formula* f, unsigned from, unsigned to)
{
  SingleVarRenaming renaming{from, TermList::var(to)};
  return SubstHelper::apply(f, renaming);
}

bool Miniscoping::sameVarList(const VSList* a, const VSList* b)
{
  while (VSList::isNonEmpty(a) && VSList::isNonEmpty(b)) {
    if (a->head() != b->head()) {
      return false;
    }
    a = a->tail();
    b = b->tail();
  }
  return VSList::isEmpty(a) && VSList::isEmpty(b);
}

/**
 * Miniscope a formula, bottom-up: a quantifier block is only pushed
 * after its body has been fully miniscoped. One such pass suffices,
 * because pushing an outer quantifier never modifies anything below
 * an already placed inner one.
 *
 * Returns the very same formula object when nothing changed.
 */
Formula* Miniscoping::apply(Formula* f)
{
  Connective con = f->connective();
  switch (con) {
  case TRUE:
  case FALSE:
  case LITERAL:
  case BOOL_TERM:
  // NNF input contains no NOT/IMP/IFF/XOR nodes; opaque is still sound
  case NOT:
  case IMP:
  case IFF:
  case XOR:
    return f;

  case AND:
  case OR:
    {
      bool changed = false;
      FormulaList::FIFO args;
      FormulaList::Iterator it(f->args());
      while (it.hasNext()) {
        Formula* c = it.next();
        Formula* m = apply(c);
        if (m != c) {
          changed = true;
        }
        if (m->connective() == con) {
          // e.g. a quantifier distributed into an AND right under an AND;
          // splice the junct in, to keep the result flattened
          changed = true;
          FormulaList::Iterator sub(m->args());
          while (sub.hasNext()) {
            args.pushBack(sub.next());
          }
        } else {
          args.pushBack(m);
        }
      }
      if (!changed) {
        return f;
      }
      // miniscoping the juncts does not change their free variables
      return reg(new JunctionFormula(con, args.list()), _fv.get(f));
    }

  case FORALL:
  case EXISTS:
    {
      Formula* g = apply(f->qarg());
      Formula* res = pushBlock(con, f->vars(), g);
      if (g == f->qarg() && res->connective() == con &&
          res->qarg() == g && sameVarList(res->vars(), f->vars())) {
        return f; // the block reproduced itself; keep sharing
      }
      return res;
    }

  case NAME:
  case NOCONN:
    ASSERTION_VIOLATION;
  }

  ASSERTION_VIOLATION;
} // Miniscoping::apply

/**
 * Push the variables of one quantifier block independently into @c g,
 * innermost (i.e. last) variable first; a variable that cannot move
 * gets stuck outside the previously placed ones, so a fully stuck
 * block reassembles in the original variable order.
 */
Formula* Miniscoping::pushBlock(Connective q, VSList* vars, Formula* g)
{
  ASS(q == FORALL || q == EXISTS);

  Stack<VarSort> vs(4);
  VSList::Iterator it(vars);
  while (it.hasNext()) {
    vs.push(it.next());
  }
  while (vs.isNonEmpty()) {
    g = pushVar(q, vs.pop(), g);
  }
  return g;
} // Miniscoping::pushBlock

/**
 * Push a single quantified variable as deep into @c g as possible.
 *
 * The result's top-level connective is always either @c g's one or @c q,
 * which keeps the output flattened by construction.
 */
Formula* Miniscoping::pushVar(Connective q, VarSort vs, Formula* g)
{
  unsigned x = vs.first;

  if (!_fv.get(g)->member(x)) {
    return g; // dummy quantifier drop
  }

  // any result built below binds x, so its free variables are these
  VarSet* resFV = minusVar(_fv.get(g), x);

  Connective dist = (q == FORALL) ? AND : OR; // distributive junction
  Connective dual = (q == FORALL) ? OR : AND;

  Connective con = g->connective();
  if (con == dist && maySplit(q)) {
    // full distribution: push into every junct containing x;
    // all but the first copy of the binder get a fresh variable,
    // keeping the result rectified
    bool first = true;
    FormulaList::FIFO args;
    FormulaList::Iterator it(g->args());
    while (it.hasNext()) {
      Formula* c = it.next();
      if (!_fv.get(c)->member(x)) {
        args.pushBack(c);
      } else if (first) {
        first = false;
        args.pushBack(pushVar(q, vs, c));
      } else {
        unsigned x2 = _nextVar++;
        Formula* r = rename(c, x, x2);
        computeFV(r); // analyse the fresh copy before pushing into it
        args.pushBack(pushVar(q, VarSort(x2, vs.second), r));
      }
    }
    return reg(new JunctionFormula(dist, args.list()), resFV);
  }

  if (con == dual || con == dist) {
    // partition the juncts by occurrence of x
    // (for the dist junction we only get here when splitting is forbidden)
    Stack<Formula*> juncts(8);
    Stack<bool> hasX(8);
    unsigned withXCnt = 0;
    FormulaList::Iterator it(g->args());
    while (it.hasNext()) {
      Formula* c = it.next();
      bool occurs = _fv.get(c)->member(x);
      juncts.push(c);
      hasX.push(occurs);
      if (occurs) {
        withXCnt++;
      }
    }
    ASS_G(withXCnt,0); // x is free in g

    if (withXCnt == juncts.size()) {
      // every junct contains x: the quantifier is stuck here
      return reg(new QuantifiedFormula(q, VSList::singleton(vs), g), resFV);
    }

    Formula* core = nullptr;
    if (withXCnt == 1) {
      // push deeper into the single junct containing x
      for (unsigned i = 0; i < juncts.size(); i++) {
        if (hasX[i]) {
          core = pushVar(q, vs, juncts[i]);
          break;
        }
      }
    } else {
      // several juncts contain x: quantify their junction
      // (provably stuck at the dual junction, stuck by policy at dist)
      FormulaList::FIFO withX;
      VarSet* withXFV = VarSet::getEmpty();
      for (unsigned i = 0; i < juncts.size(); i++) {
        if (hasX[i]) {
          withX.pushBack(juncts[i]);
          withXFV = withXFV->getUnion(_fv.get(juncts[i]));
        }
      }
      Formula* inner = reg(new JunctionFormula(con, withX.list()), withXFV);
      core = reg(new QuantifiedFormula(q, VSList::singleton(vs), inner),
                 minusVar(withXFV, x));
    }
    ASS(core);

    // rebuild in the original junct order, with core replacing
    // the first junct containing x
    FormulaList::FIFO args;
    bool coreDone = false;
    for (unsigned i = 0; i < juncts.size(); i++) {
      if (hasX[i]) {
        if (!coreDone) {
          args.pushBack(core);
          coreDone = true;
        }
      } else {
        args.pushBack(juncts[i]);
      }
    }
    return reg(new JunctionFormula(con, args.list()), resFV);
  }

  if (con == q) {
    // rectifiedness ensures x is not among g's own variables;
    // try pushing past them (a sound quantifier swap)
    Formula* h = pushVar(q, vs, g->qarg());
    if (h->connective() == q) {
      // got stuck right below g's block: merge the blocks,
      // with the pushed variable in front (it came from outside)
      return reg(new QuantifiedFormula(q, VSList::append(h->vars(), g->vars()), h->qarg()),
                 resFV);
    }
    return reg(new QuantifiedFormula(q, g->vars(), h), resFV);
  }

  // anything else (a literal, the opposite quantifier, ...): stuck
  return reg(new QuantifiedFormula(q, VSList::singleton(vs), g), resFV);
} // Miniscoping::pushVar

}
