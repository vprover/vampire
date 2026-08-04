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
 * @file Miniscoping.hpp
 * Defines class Miniscoping implementing the miniscoping transformation:
 * pushing quantifiers inside formulas to minimize their scope.
 */

#ifndef __Miniscoping__
#define __Miniscoping__

#include "Forwards.hpp"

#include "Kernel/Formula.hpp"

#include "Lib/DHMap.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Miniscoping: push quantifiers inwards on rectified, NNF, flattened formulas,
 * to be applied just before Skolemization (cf. Preprocess::preprocess3),
 * so that Skolem functions get fewer arguments.
 *
 * The transformation rules (Q a quantifier, J its distributive junction,
 * i.e. and for forall / or for exists, D the dual one):
 * - (Q x)F -> F, when x is not free in F
 * - (Q x)(F1 J ... J Fn) -> (Q x)F1 J ... J (Q x)Fn, pushing into each juct
 *   containing x (fresh variables keep the result rectified)
 * - (Q x)(F1 D ... D Fn) -> (Q x)(Fi1 D ... D Fik) D Fj1 D ... D Fjm,
 *   where Fi1,...,Fik are exactly the juncts containing x
 * - multi-variable blocks (Q x1,...,xn)F are split and each variable
 *   pushed independently as deep as possible
 *
 * The output is again rectified, NNF and flattened.
 */
class Miniscoping
{
public:
  static FormulaUnit* miniscope(FormulaUnit* unit);
  static Formula* miniscope(Formula* f)
  {
    Miniscoping ms;
    ms.computeFV(f);
    Formula* res = ms.apply(f);
    res->label(f->getLabel());
    return res;
  }

private:
  Miniscoping() : _nextVar(0) {}

  VarSet* computeFV(Formula* f);
  Formula* apply(Formula* f);
  Formula* pushBlock(Connective q, VSList* vars, Formula* g);
  Formula* pushVar(Connective q, VarSort vs, Formula* g);

  /** Record the free variables of a newly built formula and return it. */
  Formula* reg(Formula* f, VarSet* fv)
  {
    ALWAYS(_fv.insert(f, fv));
    return f;
  }

  static Formula* rename(Formula* f, unsigned from, unsigned to);
  static bool sameVarList(const VSList* a, const VSList* b);

  /** free variables of every (sub)formula node: seeded by computeFV
      and maintained for the nodes built during the transformation,
      so that "does x occur in c" is a lookup and not a traversal */
  DHMap<Formula*, VarSet*> _fv;
  /** the least variable index not occurring (free or bound) in the unit being processed */
  unsigned _nextVar;
}; // class Miniscoping

}

#endif
