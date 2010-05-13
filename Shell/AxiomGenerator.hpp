/**
 * @file AxiomGenerator.hpp

 * Defines class AxiomGenerator.
 */

#ifndef __AxiomGenerator__
#define __AxiomGenerator__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"
#include "../Lib/DHSet.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Theory.hpp"


namespace Shell
{

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
TermBlock operator++(const TermBlock& b1,int);


FormBlock operator!(const FormBlock& f);
FormBlock operator|(const FormBlock& l, const FormBlock& r);
FormBlock operator&(const FormBlock& l, const FormBlock& r);


//the followint is to allow having --> stand for an implication
struct HalfImpl {
  HalfImpl(const FormBlock& fb) : fb(fb) {}
  FormBlock fb;
};

HalfImpl operator--(const FormBlock& l, int);
FormBlock operator>(const HalfImpl& l, const FormBlock& r);

//the followint is to allow having --> stand for an implication
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
  virtual void enumerate() = 0;

  void axiom(FormBlock b);

  TermBlock X0,X1,X2,X3,X4;
  LazyConstant zero;
private:
  UnitList* _acc;

  DHSet<Interpretation> _presentElements;
};

};

#endif /* __AxiomGenerator__ */
