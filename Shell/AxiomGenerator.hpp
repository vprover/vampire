
/*
 * File AxiomGenerator.hpp.
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
 * @file AxiomGenerator.hpp

 * Defines class AxiomGenerator.
 */

#ifndef __AxiomGenerator__
#define __AxiomGenerator__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"


namespace Shell
{
#if 1

#else

using namespace Kernel;

namespace AxGen
{

struct FormBlock
{
public:
  FormBlock() {}
  FormBlock(Formula* f) : form(f) {}

  Formula* form;
};

struct TermBlock
{
public:
  TermBlock()  {}
  TermBlock(TermList t) : term(t) {}

  TermList term;
};

struct LazyConstant
{
public:
  LazyConstant() {}
  LazyConstant(InterpretedType val) : val(val) {}
  operator TermBlock();

  InterpretedType val;
};

TermBlock var(unsigned num);

TermBlock fun(Interpretation te, const TermBlock* args);
TermBlock fun(unsigned fn, const TermBlock* args);

FormBlock pred(Interpretation te, bool positive, const TermBlock* args);
FormBlock pred(unsigned pred, bool positive, const TermBlock* args);

TermBlock iConst(InterpretedType val);
TermBlock fun0(Interpretation te);
TermBlock fun1(Interpretation te, const TermBlock& b1);
TermBlock fun2(Interpretation te, const TermBlock& b1, const TermBlock& b2);
FormBlock pred2(Interpretation te, bool positive, const TermBlock& b1, const TermBlock& b2);

FormBlock operator==(const TermBlock& b1, const TermBlock& b2);
FormBlock operator!=(const TermBlock& b1, const TermBlock& b2);

FormBlock operator>(const TermBlock& b1, const TermBlock& b2);
FormBlock operator<=(const TermBlock& b1, const TermBlock& b2);
FormBlock operator<(const TermBlock& b1, const TermBlock& b2);
FormBlock operator>=(const TermBlock& b1, const TermBlock& b2);

TermBlock operator+(const TermBlock& b1, const TermBlock& b2);
TermBlock operator-(const TermBlock& b1, const TermBlock& b2);
TermBlock operator*(const TermBlock& b1, const TermBlock& b2);
TermBlock operator/(const TermBlock& b1, const TermBlock& b2);

TermBlock operator-(const TermBlock& b1);
TermBlock operator++(const TermBlock& b1,int);


FormBlock operator!(const FormBlock& f);
FormBlock operator|(const FormBlock& l, const FormBlock& r);
FormBlock operator&(const FormBlock& l, const FormBlock& r);


//the following is to allow having --> stand for an implication
struct HalfImpl {
  HalfImpl(const FormBlock& fb) : fb(fb) {}
  FormBlock fb;
};

HalfImpl operator--(const FormBlock& l, int);
FormBlock operator>(const HalfImpl& l, const FormBlock& r);

//the following is to allow having -=- stand for an equivalence
struct HalfEquiv {
  HalfEquiv(const FormBlock& fb) : fb(fb) {}
  FormBlock fb;
};

FormBlock operator-=(const FormBlock& l, const HalfEquiv& r);
HalfEquiv operator-(const FormBlock& l);


};

using namespace AxGen;

class AxiomGenerator
{
public:
  UnitList* getAxioms();

  bool has(Interpretation el) const { return _presentElements.find(el); }
  void include(Interpretation el) { _presentElements.insert(el); }
protected:
  /**
   * In this function, neccessary axioms are be included into the problem by 
   * call to the @b axiom function. The decision on axiom inclusion should 
   * be done based on presence of interpreted symbols which is queried by the 
   * @b has function.
   */
  virtual void enumerate() = 0;
  /**
   * In this function, neccessary interpreted symbols should be included
   * into the problem by call to the @b include function. The decision on
   * symbol inclusion should be done based on presence of other interpreted 
   * symbols which is queried by the @b has function.
   */
  virtual void inclusionImplications() = 0;

  void axiom(FormBlock b);


  FormBlock ex(TermBlock var, FormBlock form);

  TermBlock idiv(TermBlock arg1, TermBlock arg2);

  FormBlock igt(TermBlock arg1, TermBlock arg2);
  FormBlock ilt(TermBlock arg1, TermBlock arg2);
  FormBlock ige(TermBlock arg1, TermBlock arg2);
  FormBlock ile(TermBlock arg1, TermBlock arg2);
  
  TermBlock X0,X1,X2,X3,X4;
  LazyConstant zero;
  LazyConstant one;
private:
  UnitList* _acc;

  DHSet<Interpretation> _presentElements;
};

#endif

};

#endif /* __AxiomGenerator__ */
