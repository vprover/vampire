/**
 * @file SMTFormula.hpp
 * Defines class SMTFormula.
 */

#ifndef __SMTFormula__
#define __SMTFormula__

#include <iosfwd>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"

namespace Shell {

using namespace Lib;

struct SMTConstant;


struct SMTFormula__HalfImpl;
struct SMTFormula__HalfEquiv;

class SMTFormula
{
protected:
  SMTFormula(string val) : _val(val) {}
public:
  static SMTFormula getTrue() { return SMTFormula("true"); }
  static SMTFormula getFalse() { return SMTFormula("false"); }

  static SMTConstant unsignedValue(unsigned val);
  static SMTConstant name(string name);
  static SMTConstant name(string n1, string n2);

  static SMTFormula equals(SMTFormula f1, SMTFormula f2)
  { return SMTFormula("(= " + f1._val + " " + f2._val + ")"); }

  static SMTFormula condNumber(SMTFormula condition, unsigned value);

  static SMTFormula multiply(SMTFormula f1, SMTFormula f2)
  { return SMTFormula("(* " + f1._val + " " + f2._val + ")"); }

  static SMTFormula add(SMTFormula f1, SMTFormula f2)
  { return SMTFormula("(+ " + f1._val + " " + f2._val + ")"); }

  static SMTFormula conjunction(const SMTFormula& f1, const SMTFormula& f2);
  static SMTFormula disjunction(const SMTFormula& f1, const SMTFormula& f2);


  bool isTrue() const { return _val=="true"; }
  bool isFalse() const { return _val=="false"; }

  operator string() const { return _val; }

  SMTFormula operator!() const
  { return SMTFormula("(not " + _val + ")"); }

  SMTFormula operator&(const SMTFormula& f) const
  { return conjunction(*this, f); }

  SMTFormula operator|(const SMTFormula& f) const
  { return disjunction(*this, f); }


  //this is to allow having --> stand for an implication
  SMTFormula__HalfImpl operator--(int) const;

  //these are to allow having -=- stand for an equivalence
  SMTFormula__HalfEquiv operator-() const;
  SMTFormula operator-=(const SMTFormula__HalfEquiv& r) const;


  string toString() const { return _val; }
private:
  friend class SMTFormula__HalfImpl;
  friend class SMTFormula__HalfEquiv;

  string _val;
};

//the following is to allow having --> stand for an implication
struct SMTFormula__HalfImpl {
  SMTFormula operator>(const SMTFormula& r) const
  { return SMTFormula("(implies " + pf._val + " " + r._val + ")"); }
private:
  friend class SMTFormula;
  SMTFormula__HalfImpl(const SMTFormula& pf) : pf(pf) {}
  SMTFormula pf;
};

//the following is to allow having -=- stand for an equivalence
struct SMTFormula__HalfEquiv {
private:
  friend class SMTFormula;
  SMTFormula__HalfEquiv(const SMTFormula& pf) : pf(pf) {}
  SMTFormula pf;
};


class SMTConstant : public SMTFormula
{
  friend class SMTFormula;

  SMTConstant(string val) : SMTFormula(val) {}
};


class SMTBenchmark
{
public:

  void declarePropositionalConstant(SMTConstant pred);
  void declareRealConstant(SMTConstant pred);

  void addFormula(const SMTFormula& f, string comment="");

  void output(ostream& out);
private:
  typedef DHSet<string> StringSet;
  typedef DHMap<string,string> StringMap;

  StringSet _predDecls;
  StringMap _funDecls;

  Stack<SMTFormula> _formulas;
  Stack<string> _formulaComments;
};



}

#endif // __SMTFormula__
