/**
 * @file TheoryAxioms.cpp
 * Implements class TheoryAxioms.
 */

#include "../Lib/Environment.hpp"

#include "../Kernel/Signature.hpp"

#include "AxiomGenerator.hpp"
#include "Property.hpp"
#include "SymCounter.hpp"

#include "TheoryAxioms.hpp"

namespace Shell
{
using namespace Lib;
using namespace Kernel;

struct TheoryAxioms::Arithmetic
: public AxiomGenerator
{
  void inclusionImplications()
  {
    if(has(Theory::GREATER_EQUAL) || has(Theory::LESS) || has(Theory::LESS_EQUAL)) {
      include(Theory::GREATER);
    }
    if(has(Theory::MINUS)) {
      include(Theory::PLUS);
    }
    if(has(Theory::PLUS)) {
      include(Theory::SUCCESSOR);
    }
    if(has(Theory::DIVIDE)) {
      include(Theory::MULTIPLY);
    }
  }
  void enumerate()
  {
    if(has(Theory::GREATER_EQUAL)) {
      axiom( (X0>=X1) -=- !(X1>X0) );
    }
    if(has(Theory::LESS)) {
      axiom( (X0<X1) -=- (X1>X0) );
    }
    if(has(Theory::LESS_EQUAL)) {
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
    if(has(Theory::MINUS)) {
      axiom( (X0-X1==X2) -=- (X0==X1+X2) );
    }
    if(has(Theory::PLUS)) {
      axiom( X0+X1==X1+X0 );
      axiom( (X0+X1)+X2==X0+(X1+X2) );
      axiom( X0+zero==X0 );
      axiom( X0+(X1++)==(X0+X1)++ );

      if(has(Theory::GREATER)) {
	axiom( (X0+X1>X0+X2) -=- (X1>X2) );
      }
    }
    if(has(Theory::MULTIPLY)) {
      axiom( X0*X1==X1*X0 );
      axiom( (X0*X1)*X2==X0*(X1*X2) );
      axiom( X0*one==X0 );
      axiom( X0*zero==zero );
      
      if(has(Theory::PLUS)) {
        axiom( X0*(X1++)==(X0*X1)+X0 );
	axiom( (X0+X1)*(X2+X3) == (X0*X2 + X0*X3 + X1*X2 + X1*X3) );
      }
    }
    if(has(Theory::DIVIDE)) {
      axiom( (X1!=zero) --> ( (X0/X1==X2) -=- (X1*X2==X0) ) );
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
