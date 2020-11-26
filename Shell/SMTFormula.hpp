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

class SMTConstant;


struct SMTFormula__HalfImpl;
struct SMTFormula__HalfEquiv;

class SMTFormula
{
protected:
  SMTFormula(vstring val) : _val(val) {}
public:
  static SMTFormula getTrue() { return SMTFormula("true"); }
  static SMTFormula getFalse() { return SMTFormula("false"); }

  static SMTConstant unsignedValue(unsigned val);
  static SMTConstant name(vstring name);
  static SMTConstant name(vstring n1, vstring n2);

  static SMTFormula equals(SMTFormula f1, SMTFormula f2)
  { return SMTFormula("(= " + f1._val + " " + f2._val + ")"); }

  static SMTFormula less(SMTFormula f1, SMTFormula f2)
  { return SMTFormula("(< " + f1._val + " " + f2._val + ")"); }

  static SMTFormula condNumber(SMTFormula condition, unsigned value);

  static SMTFormula multiply(SMTFormula f1, SMTFormula f2)
  { return SMTFormula("(* " + f1._val + " " + f2._val + ")"); }

  static SMTFormula add(SMTFormula f1, SMTFormula f2)
  { return SMTFormula("(+ " + f1._val + " " + f2._val + ")"); }

  static SMTFormula conjunction(const SMTFormula& f1, const SMTFormula& f2);
  static SMTFormula disjunction(const SMTFormula& f1, const SMTFormula& f2);


  bool isTrue() const { return _val=="true"; }
  bool isFalse() const { return _val=="false"; }

  operator vstring() const { return _val; }

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


  vstring toString() const { return _val; }
private:
  friend struct SMTFormula__HalfImpl;
  friend struct SMTFormula__HalfEquiv;

  vstring _val;
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

  SMTConstant(vstring val) : SMTFormula(val) {}
};


class SMTBenchmark
{
public:

  void declarePropositionalConstant(SMTConstant pred);
  void declareRealConstant(SMTConstant pred);

  void addFormula(const SMTFormula& f, vstring comment="");
  void popFormula();

  void output(ostream& out);
private:
  typedef DHSet<vstring> StringSet;
  typedef DHMap<vstring,vstring> StringMap;

  StringSet _predDecls;
  StringMap _funDecls;

  Stack<SMTFormula> _formulas;
  Stack<vstring> _formulaComments;
};

class SMTSolverResult
{
public:
  enum Status
  {
    SAT, UNSAT, UNKNOWN
  };

  Status status;
  DHMap<vstring,vstring> assignment;

  void reset()
  {
    status = UNKNOWN;
    assignment.reset();
  }
};

class SMTSolver
{
public:
  virtual ~SMTSolver() {}

  void run(SMTBenchmark& problem, SMTSolverResult& res)
  {
    run(problem, res, 0);
  }

  enum MinimizationResult
  {
    EXACT,
    APPROXIMATE,
    FAIL
  };

  /**
   * timeout equal to 0 means unlimited
   */
  virtual void run(SMTBenchmark& problem, SMTSolverResult& res, unsigned timeout) = 0;

  MinimizationResult minimize(SMTBenchmark& problem, SMTConstant costFn, SMTSolverResult& res);

private:
  SMTSolverResult::Status tryUpperBound(SMTBenchmark& problem, SMTConstant costFn, unsigned val, SMTSolverResult& res);
};

class YicesSolver : public SMTSolver
{
public:
  virtual void run(SMTBenchmark& problem, SMTSolverResult& res, unsigned timeout);
};

}

#endif // __SMTFormula__
