/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"

#include "Inferences/ForwardGroundJoinability.hpp"

TermIndex<DemodulatorData>* demodulationLhsIndex(const SaturationAlgorithm& salg) {
  return new DemodulationLHSIndex(new CodeTreeTIS<DemodulatorData>(), salg.getOrdering(), salg.getOptions());
}

TEST_FUN(joinability_test01) {
  DECL_DEFAULT_VARS
  DECL_VAR(u, 3)
  DECL_SORT(srt)
  DECL_FUNC (f, {srt, srt}, srt)

  // set up saturation algorithm
  auto container = PlainClauseContainer();
  const ClauseStack context = {
    clause({ f(x,y) == f(y,x) }),
    clause({ f(f(x,y),z) == f(x,f(y,z)) }),
    clause({ f(x,f(y,z)) == f(y,f(z,x)) }),
  };

  // init problem
  Problem p;
  auto ul = UnitList::empty();
  UnitList::pushFromIterator(ClauseStack::ConstRefIterator(context), ul);
  p.addUnits(ul);
  env.setMainProblem(&p);

  Options o;
  Test::MockedSaturationAlgorithm salg(p, o);
  const Stack<Index*>& indices = { demodulationLhsIndex(salg) };

  ForwardGroundJoinability fgj(o);
  fgj.setTestIndices(indices);
  fgj.InferenceEngine::attach(&salg);
  for (auto i : indices) {
    i->attachContainer(&container);
  }

  // add the clauses to the index
  for (auto c : context) {
    c->setStore(Clause::ACTIVE);
    container.add(c);
  }

  ClauseIterator replacements;
  ClauseIterator premises;

  // these 3 are the only non-redundant equations from all possible AC-derived axioms
  ASS(!fgj.perform(clause({ f(x,y) == f(y,x) }), replacements, premises));
  ASS(!fgj.perform(clause({ f(f(x,y),z) == f(x,f(y,z)) }), replacements, premises));
  ASS(!fgj.perform(clause({ f(x,f(y,z)) == f(y,f(x,z)) }), replacements, premises));

  ASS(fgj.perform(clause({ f(f(x,y),z) == f(f(x,y),z) }), replacements, premises));
  ASS(fgj.perform(clause({ f(f(x,y),z) == f(f(x,z),y) }), replacements, premises));
  ASS(fgj.perform(clause({ f(f(x,y),z) == f(f(y,x),z) }), replacements, premises));
  ASS(fgj.perform(clause({ f(f(x,y),z) == f(f(y,z),x) }), replacements, premises));
  ASS(fgj.perform(clause({ f(f(x,y),z) == f(f(z,x),y) }), replacements, premises));
  ASS(fgj.perform(clause({ f(f(x,y),z) == f(f(z,y),x) }), replacements, premises));

  // ASS(fgj.perform(clause({ f(f(x,y),z) == f(x,f(z,y)) }), replacements, premises));
  // ASS(fgj.perform(clause({ f(f(x,y),z) == f(y,f(x,z)) }), replacements, premises));
  // ASS(fgj.perform(clause({ f(f(x,y),z) == f(y,f(z,x)) }), replacements, premises));
  ASS(fgj.perform(clause({ f(f(x,y),z) == f(z,f(x,y)) }), replacements, premises));
  // ASS(fgj.perform(clause({ f(f(x,y),z) == f(z,f(y,x)) }), replacements, premises));

  // ASS(fgj.perform(clause({ f(x,f(y,z)) == f(f(x,y),z) }), replacements, premises));
  ASS(fgj.perform(clause({ f(x,f(y,z)) == f(f(x,z),y) }), replacements, premises));
  // ASS(fgj.perform(clause({ f(x,f(y,z)) == f(f(y,x),z) }), replacements, premises));
  ASS(fgj.perform(clause({ f(x,f(y,z)) == f(f(y,z),x) }), replacements, premises));
  ASS(fgj.perform(clause({ f(x,f(y,z)) == f(f(z,x),y) }), replacements, premises));
  ASS(fgj.perform(clause({ f(x,f(y,z)) == f(f(z,y),x) }), replacements, premises));

  ASS(fgj.perform(clause({ f(x,f(y,z)) == f(x,f(y,z)) }), replacements, premises));
  // ASS(fgj.perform(clause({ f(x,f(y,z)) == f(x,f(z,y)) }), replacements, premises));
  // ASS(fgj.perform(clause({ f(x,f(y,z)) == f(y,f(z,x)) }), replacements, premises));
  // ASS(fgj.perform(clause({ f(x,f(y,z)) == f(z,f(x,y)) }), replacements, premises));
  // ASS(fgj.perform(clause({ f(x,f(y,z)) == f(z,f(y,x)) }), replacements, premises));

  ASS(fgj.perform(clause({ f(x,f(y,f(z,u))) == f(z,f(x,f(y,u))) }), replacements, premises));
  ASS(fgj.perform(clause({ f(x,f(y,f(z,u))) == f(u,f(x,f(y,z))) }), replacements, premises));
  ASS(fgj.perform(clause({ f(x,f(y,f(z,u))) == f(z,f(y,f(x,u))) }), replacements, premises));
  ASS(fgj.perform(clause({ f(x,f(y,f(z,u))) == f(z,f(u,f(y,x))) }), replacements, premises));
  ASS(fgj.perform(clause({ f(y,f(x,f(z,u))) == f(u,f(x,f(y,z))) }), replacements, premises));
  ASS(fgj.perform(clause({ f(x,f(y,f(z,u))) == f(y,f(z,f(u,x))) }), replacements, premises));
  // ...

  // tear down saturation algorithm
  fgj.InferenceEngine::detach();
}
