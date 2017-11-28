
/*
 * File TestUtils.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TestUtils.cpp
 * Implements class TestUtils.
 */

#include <cstdarg>


#include "Lib/List.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/AIG.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"

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
    Formula* form = u->getFormula();
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

  UnitList* units = 0;
  while(afit.hasNext()) {
    Api::AnnotatedFormula af = afit.next();
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

SAT::SATClause* TestUtils::buildSATClause(unsigned len,...)
{
  using namespace SAT;

  va_list litArgs;
  va_start(litArgs,len);

  static SATLiteralStack lits;
  lits.reset();
  for(unsigned i=0; i<len; ++i) {
    int litVal = va_arg(litArgs, int);
    bool pos = litVal>0;
    unsigned var = pos ? litVal : -litVal;
    lits.push(SATLiteral(var, pos));
  }

  va_end(litArgs);

  return SATClause::fromStack(lits);
}

}
