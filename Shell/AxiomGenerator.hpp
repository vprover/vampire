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


namespace Shell
{

using namespace Kernel;

namespace AxGen
{

enum TheoryElement
{
  //predicates
  EQUAL,
  GREATER,
  GREATER_EQUAL,
  LESS,
  LESS_EQUAL,

  //functions
  PLUS,
  SUCCESSOR,
  ZERO

};

class Context
{
public:
  void interpret(TheoryElement el, unsigned num);

  unsigned pred(TheoryElement el);
  unsigned fun(TheoryElement el);
  bool supported(TheoryElement el);
  bool has(TheoryElement el) const { return _usedElements.find(el); }
  void include(TheoryElement el) { _usedElements.insert(el); }

  unsigned arity(TheoryElement el);
  bool isFunction(TheoryElement el);
private:
  DHMap<TheoryElement,unsigned> _interpretation;
  DHSet<TheoryElement> _usedElements;
};

struct FormBlock
{
public:
  FormBlock() : ctx(ctx) {}
  FormBlock(Context* ctx, Formula* f) : ctx(ctx), form(f) {}

  Context* ctx;
  Formula* form;
};

struct TermBlock
{
public:
  TermBlock() : ctx(0) {}
  TermBlock(Context* ctx, TermList t) : ctx(ctx), term(t) {}

  Context* ctx;
  TermList term;
};

struct LazyConstant
{
public:
  LazyConstant() : ctx(0) {}
  LazyConstant(TheoryElement te, Context* ctx) : ctx(ctx), te(te) {}
  operator TermBlock();

  Context* ctx;
  TheoryElement te;
};

TermBlock var(unsigned num, Context* ctx);

TermBlock fun(TheoryElement te, const TermBlock* args, Context* ctx=0);
TermBlock fun(unsigned fn, const TermBlock* args, Context* ctx=0);

FormBlock pred(TheoryElement te, bool positive, const TermBlock* args, Context* ctx=0);
FormBlock pred(unsigned pred, bool positive, const TermBlock* args, Context* ctx=0);

TermBlock fun0(TheoryElement te, Context* ctx);
TermBlock fun1(TheoryElement te, const TermBlock& b1);
TermBlock fun2(TheoryElement te, const TermBlock& b1, const TermBlock& b2);
FormBlock pred2(TheoryElement te, bool positive, const TermBlock& b1, const TermBlock& b2);

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
  UnitList* getAxioms(Context* ctx);
protected:
  virtual void enumerate() = 0;

  void axiom(FormBlock b);
  bool has(TheoryElement el) const { return _ctx->has(el); }
  void include(TheoryElement el) { return _ctx->include(el); }

  TermBlock X0,X1,X2,X3,X4;
  LazyConstant zero;
private:
  Context* _ctx;
  UnitList* _acc;
};

};

void testAxGen();

#endif /* __AxiomGenerator__ */
