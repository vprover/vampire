/**
 * @file TheoryAxioms.cpp
 * Implements class TheoryAxioms.
 */

#include "../Lib/Environment.hpp"

#include "../Kernel/Signature.hpp"

#include "AxiomGenerator.hpp"
#include "Property.hpp"q
#include "SymCounter.hpp"

#include "TheoryAxioms.hpp"

namespace Shell
{
using namespace Lib;
using namespace Kernel;

struct TheoryAxioms::Arithmetic
: public AxiomGenerator
{
  void enumerate()
  {
    if(has(Theory::GREATER_EQUAL)) {
      include(Theory::GREATER);
      axiom( (X0>=X1) -=- !(X1>X0) );
    }
    if(has(Theory::LESS)) {
      include(Theory::GREATER);
      axiom( (X0<X1) -=- (X1>X0) );
    }
    if(has(Theory::LESS_EQUAL)) {
      include(Theory::GREATER);
      axiom( (X0<=X1) -=- !(X0>X1) );
    }
    if(has(Theory::GREATER)) {
      axiom( !(X0>X0) );
      axiom( (X0>X1) --> !(X1>X0) );
      axiom( ((X0>X1) & (X1>X2)) --> (X0>X2) );
      if(has(Theory::SUCCESSOR)) {
	axiom( X0++>X0 );
      }
    }
    if(has(Theory::PLUS)) {
      include(Theory::SUCCESSOR);

      axiom( X0+X1==X1+X0 );
      axiom( (X0+X1)+X2==X0+(X1+X2) );
      axiom( X0+zero==X0 );
      axiom( X0+(X1++)==(X0+X1)++ );

      if(has(Theory::GREATER)) {
	axiom( (X0+X1>X0+X2) -=- (X1>X2) );
      }
    }

  }
};

void TheoryAxioms::apply(UnitList*& units, Property* prop)
{

  Arithmetic axGen;

  //find out which symbols are used in the problem
  SymCounter sctr(*env.signature);
  sctr.count(units,1);
  for(unsigned i=0;i<Theory::interpretationElementCount; i++) {
    Interpretation interp=static_cast<Interpretation>(i);
    if(!env.signature->haveInterpretingSymbol(interp)) {
      continue;
    }
    if(Theory::isFunction(interp)) {
      unsigned fn=env.signature->getInterpretingSymbol(interp);
      if(sctr.getFun(fn).occ()) {
	axGen.include(interp);
      }
    }
    else {
      unsigned pred=env.signature->getInterpretingSymbol(interp);
      SymCounter::Pred* pc=&sctr.getPred(pred);
      if(pc->pocc() || pc->nocc() || pc->docc()) {
	axGen.include(interp);
      }
    }
  }

  UnitList* newAxioms=axGen.getAxioms();

  if(newAxioms) {
    prop->scan(newAxioms);
  }

  units=UnitList::concat(newAxioms, units);
}


}
