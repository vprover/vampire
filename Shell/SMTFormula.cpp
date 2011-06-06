/**
 * @file SMTFormula.cpp
 * Implements class SMTFormula.
 */

#include <ostream>

#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Sort.hpp"

#include "SMTFormula.hpp"

namespace Shell
{

SMTConstant SMTFormula::unsignedValue(unsigned val)
{
  CALL("SMTFormula::unsignedValue");

  return SMTConstant(Int::toString(val)+".0");
}

SMTConstant SMTFormula::name(string name)
{
  CALL("SMTFormula::name/1");

  return SMTConstant(name);
}

SMTConstant SMTFormula::name(string n1, string n2)
{
  CALL("SMTFormula::name/2");

  return SMTConstant(n1 + "_" + n2);
}


SMTFormula SMTFormula::condNumber(SMTFormula condition, unsigned value)
{
  CALL("SMTFormula::condNumber");

  return SMTFormula("(ite " + condition._val + " " + unsignedValue(value)._val + " 0.0)");
}


SMTFormula SMTFormula::conjunction(const SMTFormula& f1, const SMTFormula& f2)
{
  CALL("SMTFormula::conjunction");

  if(f1.isTrue()) { return f2; }
  if(f2.isTrue()) { return f1; }
  if(f1.isFalse() || f2.isFalse()) { return getFalse(); }
  return SMTFormula("(and " + f1._val + " " + f2._val + ")");
}

SMTFormula SMTFormula::disjunction(const SMTFormula& f1, const SMTFormula& f2)
{
  CALL("SMTFormula::disjunction");

  if(f1.isFalse()) { return f2; }
  if(f2.isFalse()) { return f1; }
  if(f1.isTrue() || f2.isTrue()) { getTrue(); }
  return SMTFormula("(or " + f1._val + " " + f2._val + ")");
}



//helper operator implementation for pseudo-operators --> and -=-

SMTFormula__HalfImpl SMTFormula::operator--(int) const { return SMTFormula__HalfImpl(*this); }

SMTFormula__HalfEquiv SMTFormula::operator-() const { return SMTFormula__HalfEquiv(*this); }
SMTFormula SMTFormula::operator-=(const SMTFormula__HalfEquiv& r) const
{ return SMTFormula("(= " + _val + " " + r.pf._val + ")"); }




///////////////////////
// SMTBenchmark
//

void SMTBenchmark::addFormula(const SMTFormula& f, string comment)
{
  CALL("SMTBenchmark::addFormula");
  ASS_EQ(_formulas.size(), _formulaComments.size());

  _formulas.push(f);
  _formulaComments.push(comment);
}

void SMTBenchmark::declarePropositionalConstant(SMTConstant pred)
{
  CALL("SMTBenchmark::declarePropositionalConstant");
  ASS(!_funDecls.find(pred.toString()));

  _predDecls.insert(pred.toString());
}

void SMTBenchmark::declareRealConstant(SMTConstant pred)
{
  CALL("SMTBenchmark::declareRealConstant");
  ASS(!_predDecls.find(pred.toString()));

  _funDecls.insert(pred.toString(), "Real");
}

void SMTBenchmark::output(ostream& out)
{
  CALL("SMTBenchmark::output");

  out << "(benchmark VampireGeneratedBenchmark" << endl;

  StringMap::Iterator fdeclIt(_funDecls);
  while(fdeclIt.hasNext()) {
    string func, fType;
    fdeclIt.next(func, fType);
    out << ":extrafuns ((" << func << " " << fType << "))" <<endl;
  }

  static Stack<string> predDeclStack;
  predDeclStack.reset();
  predDeclStack.loadFromIterator(_predDecls.iterator());
  sort<DefaultComparator>(predDeclStack.begin(), predDeclStack.end());

  Stack<string>::BottomFirstIterator pdeclIt(predDeclStack);
  while(pdeclIt.hasNext()) {
    string pred = pdeclIt.next();
    out << ":extrapreds ((" << pred << "))" <<endl;
  }

  out << ":formula ( (and " << endl;

  Stack<SMTFormula>::BottomFirstIterator fit(_formulas);
  Stack<string>::BottomFirstIterator fCommentIt(_formulaComments);

  if(!fit.hasNext()) { out << "  true" << endl; }

  while(fit.hasNext()) {
    ALWAYS(fCommentIt.hasNext());

    SMTFormula form = fit.next();
    string comment = fCommentIt.next();
    out << "  " << form.toString();
    if(comment!="") {
      out << " ; " << comment;
    }
    out << endl;
  }

  out << ") )" << endl;
  out << ")" << endl;
}

}
