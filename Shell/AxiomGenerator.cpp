/**
 * @file AxiomGenerator.cpp

 * Implements class AxiomGenerator.
 */


#include "../Lib/DArray.hpp"
#include "../Lib/Environment.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"

#include "AxiomGenerator.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

namespace AxGen
{

void Context::interpret(TheoryElement el, unsigned num)
{
  CALL("Context::interpret");
  ASS( isFunction(el) ? (env.signature->functionArity(num)==arity(el)) :
      (env.signature->predicateArity(num)==arity(el)));

  ALWAYS(_interpretation.insert(el,num));
}

unsigned Context::pred(TheoryElement el)
{
  CALL("Context::pred");
  return _interpretation.get(el);
}
unsigned Context::fun(TheoryElement el)
{
  CALL("Context::fun");
  return _interpretation.get(el);
}
bool Context::supported(TheoryElement el)
{
  CALL("Context::supported");
  return _interpretation.find(el);
}

unsigned Context::arity(TheoryElement el)
{
  CALL("Context::arity");

  switch(el) {
  case EQUAL:
  case GREATER:
  case PLUS:
    return 2;
  case SUCCESSOR:
    return 1;
  case ZERO:
    return 0;
  default:
    ASSERTION_VIOLATION;
  }
}

bool Context::isFunction(TheoryElement el)
{
  CALL("Context::isFunction");

  switch(el) {
  case EQUAL:
  case GREATER:
    return false;
  case PLUS:
  case SUCCESSOR:
  case ZERO:
    return true;
  default:
    ASSERTION_VIOLATION;
  }
}


TermBlock fun0(TheoryElement te, Context* ctx)
{
  CALL("AxGen::fun0");
  ASS(ctx);
  ASS_EQ(ctx->arity(te),0);

  return fun(te, 0, ctx);
}

TermBlock fun1(TheoryElement te, const TermBlock& b1)
{
  CALL("AxGen::fun1");
  ASS(b1.ctx);
  ASS_EQ(b1.ctx->arity(te),1);

  return fun(te, &b1);
}

TermBlock fun2(TheoryElement te, const TermBlock& b1, const TermBlock& b2)
{
  CALL("AxGen::fun2");
  ASS(b1.ctx);
  ASS_EQ(b1.ctx->arity(te),2);

  TermBlock args[]={b1,b2};
  return fun(te, args);
}

FormBlock pred2(TheoryElement te, bool positive, const TermBlock& b1, const TermBlock& b2)
{
  CALL("AxGen::pred2");
  ASS(b1.ctx);
  ASS_EQ(b1.ctx->arity(te),2);

  TermBlock args[]={b1,b2};
  return pred(te, positive, args);
}

/**
 * Create function interpreted as @b te. If the function is constant,
 * @b args must be equal to 0, and @b ctx contains pointer to the context.
 * Otherwise @b ctx can be 0, and @b args points to array of @b n elements
 * where @b n is the arity of the function corresponding to @b te.
 * (Therefore the size of the array @b args is at least 1 in this case.)
 */
TermBlock fun(TheoryElement te, const TermBlock* args, Context* ctx)
{
  CALL("AxGen::fun(TheoryElement...)");

  if(ctx==0) {
    ctx=args[0].ctx;
    ASS(ctx);
  }

  if(ctx->supported(te)) {
    return fun(ctx->fun(te), args, ctx);
  }
  else {
    return TermBlock();
  }
}

/**
 * Create predicate interpreted as @b te. If the predicate is propositional,
 * @b args must be equal to 0, and @b ctx contains pointer to the context.
 * Otherwise @b ctx can be 0, and @b args points to array of @b n elements
 * where @b n is the arity of the function corresponding to @b te.
 * (Therefore the size of the array @b args is at least 1 in this case.)
 */
FormBlock pred(TheoryElement te, bool positive, const TermBlock* args, Context* ctx)
{
  CALL("AxGen::pred(TheoryElement...)");

  if(ctx==0) {
    ctx=args[0].ctx;
    ASS(ctx);
  }

  if(ctx->supported(te)) {
    return pred(ctx->pred(te), positive, args, ctx);
  }
  else {
    return FormBlock();
  }
}

TermBlock var(unsigned num, Context* ctx)
{
  CALL("AxGen::var");

  return TermBlock(ctx, TermList(num, false));
}

TermBlock fun(unsigned fn, const TermBlock* args, Context* ctx)
{
  CALL("AxGen::fun(unsigned...)");

  unsigned arity=env.signature->functionArity(fn);
  ASS(arity!=0 || ctx!=0);
  if(ctx==0) {
    ctx=args[0].ctx;
    ASS(ctx);
  }

  static DArray<TermList> targs;
  targs.ensure(arity);

  for(unsigned i=0;i<arity;i++) {
    ASS_EQ(args[i].ctx,ctx);
    targs[i]=args[i].term;
  }

  Term* t=Term::create(fn, arity, targs.array());
  return TermBlock(ctx, TermList(t));

}

FormBlock pred(unsigned pred, bool positive, const TermBlock* args, Context* ctx)
{
  CALL("AxGen::pred(unsigned...)");

  unsigned arity=env.signature->predicateArity(pred);
  ASS(arity!=0 || ctx!=0);
  if(ctx==0) {
    ctx=args[0].ctx;
    ASS(ctx);
  }

  Literal* lit;
  if(pred==0) {
    ASS_EQ(arity,2);
    lit=Literal::createEquality(positive, args[0].term, args[1].term);
  }
  else {
    static DArray<TermList> targs;
    targs.ensure(arity);

    for(unsigned i=0;i<arity;i++) {
      ASS_EQ(args[i].ctx,ctx);
      targs[i]=args[i].term;
    }
    lit=Literal::create(pred, 2, positive, false, targs.array());
  }

  return FormBlock(ctx, new AtomicFormula(lit));
}


FormBlock operator==(const TermBlock& b1, const TermBlock& b2)
{ return pred2(EQUAL, true, b1, b2); }

FormBlock operator!=(const TermBlock& b1, const TermBlock& b2)
{ return pred2(EQUAL, false, b1, b2); }

FormBlock operator>(const TermBlock& b1, const TermBlock& b2)
{ return pred2(GREATER, true, b1, b2); }

FormBlock operator<=(const TermBlock& b1, const TermBlock& b2)
{ return pred2(GREATER, false, b1, b2); }

FormBlock operator<(const TermBlock& b1, const TermBlock& b2)
{ return pred2(GREATER, true, b2, b1); }

FormBlock operator>=(const TermBlock& b1, const TermBlock& b2)
{ return pred2(GREATER, false, b2, b1); }

TermBlock operator+(const TermBlock& b1, const TermBlock& b2)
{ return fun2(PLUS, b1, b2); }

TermBlock operator++(const TermBlock& b1,int)
{ return fun1(SUCCESSOR, b1); }

HalfImpl operator--(const FormBlock& l, int)
{
  return HalfImpl(l);
}
FormBlock operator>(const HalfImpl& l, const FormBlock& r)
{
  CALL("AxGen::operator>(HalfImpl,FormBlock)");
  ASS(r.ctx);
  ASS_EQ(l.fb.ctx,r.ctx);
  return FormBlock(r.ctx, new BinaryFormula(IMP, l.fb.form, r.form));
}

};


void AxiomGenerator::axiom(FormBlock b)
{
  CALL("AxiomGenerator::axiom");

  Inference* inf=new Inference(Inference::THEORY);
  UnitList::push(new FormulaUnit(b.form, inf, Unit::AXIOM), _acc);
}

UnitList* AxiomGenerator::getAxioms(Context* ctx)
{
  CALL("AxiomGenerator::getAxioms");

  _ctx=ctx;

  zero=fun0(ZERO, _ctx);
  X0=var(0, _ctx);
  X1=var(1, _ctx);
  X2=var(2, _ctx);
  X3=var(3, _ctx);
  X4=var(4, _ctx);

  _acc=0;
  enumerate();
  return _acc;
}

};

using namespace Lib;
using namespace Kernel;
using namespace Shell;

struct PlusTestAxioms : public AxiomGenerator
{
  void enumerate()
  {
    axiom( X0+X1==X1+X0 );
    axiom( (X0+X1)+X2==X0+(X1+X2) );

    axiom( X0+zero==X0 );
    axiom( X0+(X1++)==(X0+X1)++ );

    axiom( X0++>X0 );

    axiom( (X0>X1) --> (X0!=X1) );
  }
};

void testAxGen()
{
  AxGen::Context ctx;

  ctx.interpret(AxGen::EQUAL, 0);
  ctx.interpret(AxGen::GREATER, env.signature->addPredicate("greater",2));

  ctx.interpret(AxGen::PLUS, env.signature->addFunction("plus",2));
  ctx.interpret(AxGen::SUCCESSOR, env.signature->addFunction("s",1));
  ctx.interpret(AxGen::ZERO, env.signature->addFunction("zero",0));

  UnitList* pta=PlusTestAxioms().getAxioms(&ctx);
  UnitList::Iterator uit(pta);
  while(uit.hasNext()) {
    Unit* u=uit.next();
    cout<<(u->toString())<<endl;
  }

//  The output is:
//
//  6. greater(X0,X1) => X0 != X1 [theory axiom]
//  5. greater(s(X0),X0) [theory axiom]
//  4. plus(X0,s(X1)) = s(plus(X0,X1)) [theory axiom]
//  3. plus(X0,zero) = X0 [theory axiom]
//  2. plus(X0,plus(X1,X2)) = plus(plus(X0,X1),X2) [theory axiom]
//  1. plus(X1,X0) = plus(X0,X1) [theory axiom]


}

