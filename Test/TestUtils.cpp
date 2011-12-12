/**
 * @file TestUtils.cpp
 * Implements class TestUtils.
 */

#include "Lib/List.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/AIG.hpp"

#include "TestUtils.hpp"

namespace Test
{

using namespace Kernel;
using namespace Shell;

Formula* TestUtils::getUniqueFormula(UnitList* units)
{
  CALL("TestUtils::getUniqueFormula(UnitList*)");

  FormulaList* forms = 0;
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Formula* form = u->getFormula(BDD::instance()->getFalse());
    FormulaList::push(form, forms);
  }
  Formula* conj;
  if(forms==0) {
    conj = new Formula(true);
  }
  else if(forms->tail()==0) {
    conj = forms->head();
  }
  else {
    conj = new JunctionFormula(AND, forms);
  }

  static AIGFormulaSharer sharer;
  return sharer.apply(conj).first;
}

Formula* TestUtils::getUniqueFormula(Api::AnnotatedFormulaIterator afit)
{
  CALL("TestUtils::getUniqueFormula(Api::AnnotatedFormulaIterator)");
  LOG("tu_uf", "getting unique formula for AnnotatedFormulaIterator");

  UnitList* units = 0;
  while(afit.hasNext()) {
    Api::AnnotatedFormula af = afit.next();
    LOG("tu_uf", "af: "<<af);
    UnitList::push(static_cast<Unit*>(af), units);
  }
  Formula* res = getUniqueFormula(units);
  units->destroy();
  return res;
}

Formula* TestUtils::getUniqueFormula(Api::Problem prb)
{
  CALL("TestUtils::getUniqueFormula(Api::Problem)");

  return TestUtils::getUniqueFormula(prb.formulas());
}

}
