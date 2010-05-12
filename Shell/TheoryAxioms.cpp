/**
 * @file TheoryAxioms.cpp
 * Implements class TheoryAxioms.
 */

#include "../Lib/Environment.hpp"

#include "AxiomGenerator.hpp"
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
    if(has(GREATER_EQUAL)) {
      include(GREATER);
      axiom( (X0>=X1) -=- !(X1>X0) );
    }
    if(has(LESS)) {
      include(GREATER);
      axiom( (X0<X1) -=- (X1>X0) );
    }
    if(has(LESS_EQUAL)) {
      include(GREATER);
      axiom( (X0<=X1) -=- !(X0>X1) );
    }
    if(has(GREATER)) {
      axiom( !(X0>X0) );
      axiom( (X0>X1) --> !(X1>X0) );
      axiom( ((X0>X1) & (X1>X2)) --> (X0>X2) );
    }
    if(has(PLUS)) {
      include(SUCCESSOR);

      axiom( X0+X1==X1+X0 );
      axiom( (X0+X1)+X2==X0+(X1+X2) );
      axiom( X0+zero==X0 );
      axiom( X0+(X1++)==(X0+X1)++ );

      if(has(GREATER)) {

      }
    }

  }
};

void TheoryAxioms::apply(UnitList*& units)
{
  SymCounter sctr(*env.signature);
  sctr.count(units,1);

  Arithmetic axGen;
  AxGen::Context ctx;

  UnitList* newAxioms=axGen.getAxioms(&ctx);

  units=UnitList::concat(newAxioms, units);
}


}
