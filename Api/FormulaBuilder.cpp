/**
 * @file FormulaBuilder.cpp
 * Implements class FormulaBuilder.
 */

#include "FormulaBuilder.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Map.hpp"

#include "Kernel/Connective.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Shell/TPTP.hpp"


using namespace Lib;
using namespace Shell;

namespace Api
{

struct FormulaBuilder::FBAux
{
  FBAux() : nextVar(0)
  {
  }

  /** build a term f(*args) with specified @b arity */
  Term term(const Function& f,const Term* args, unsigned arity)
  {
    CALL("FormulaBuilder::FormulaBuilder::FBAux::term");

    if(f>=static_cast<unsigned>(env.signature->functions())) {
      throw FormulaBuilderException("Function does not exist");
    }
    if(arity!=env.signature->functionArity(f)) {
      throw FormulaBuilderException("Invalid function arity: "+env.signature->functionName(f));
    }

    DArray<TermList> argArr;
    argArr.initFromArray(arity, args);

    return Kernel::TermList(Kernel::Term::create(f,arity,argArr.array()));
  }

  /** build a predicate f(t,ts) with specified @b arity */
  Formula atom(const Predicate& p, bool positive, const Term* args, unsigned arity)
  {
    CALL("FormulaBuilder::FormulaBuilder::FBAux::atom");

    if(p>=static_cast<unsigned>(env.signature->predicates())) {
      throw FormulaBuilderException("Predicate does not exist");
    }
    if(arity!=env.signature->predicateArity(p)) {
      throw FormulaBuilderException("Invalid predicate arity: "+env.signature->predicateName(p));
    }

    DArray<TermList> argArr;
    argArr.initFromArray(arity, args);

    Kernel::Literal* lit=Kernel::Literal::create(p, arity, positive, false, argArr.array());
    return new Kernel::AtomicFormula(lit);
  }

  /** indicates whether we shall check names of functions, predicates and variables */
  bool _checkNames;
  /** Map from variable namus to their numbers */
  Map<string,Var> vars;
  /** next available variable number */
  Var nextVar;
};

FormulaBuilder::FormulaBuilder(bool checkNames)
{
  CALL("FormulaBuilder::FormulaBuilder");

  _aux=new FBAux;
  _aux->_checkNames=checkNames;
}

FormulaBuilder::~FormulaBuilder()
{
  CALL("FormulaBuilder::~FormulaBuilder");

  delete _aux;
}

Var FormulaBuilder::var(const string& varName)
{
  CALL("FormulaBuilder::var");

  if(_aux->_checkNames) {
    if(!isupper(varName[0])) {
      throw InvalidTPTPNameException("Variable name must start with an uppercase character", varName);
    }
    //TODO: add further checks
  }

  Var res=_aux->vars.insert(varName, _aux->nextVar);
  if(res==_aux->nextVar) {
    _aux->nextVar++;
  }
  ASS_L(res, _aux->nextVar);
  return res;
}

Function FormulaBuilder::function(const string& funName,unsigned arity)
{
  CALL("FormulaBuilder::function");

  if(_aux->_checkNames) {
    if(!islower(funName[0])) {
      throw InvalidTPTPNameException("Function name must start with a lowercase character", funName);
    }
    //TODO: add further checks
  }

  return env.signature->addFunction(funName, arity);
}

Function FormulaBuilder::predicate(const string& predName,unsigned arity)
{
  CALL("FormulaBuilder::predicate");

  if(_aux->_checkNames) {
    if(!islower(predName[0])) {
      throw InvalidTPTPNameException("Predicate name must start with a lowercase character", predName);
    }
    //TODO: add further checks
  }

  return env.signature->addPredicate(predName, arity);
}

Term FormulaBuilder::varTerm(const Var& v)
{
  CALL("FormulaBuilder::varTerm");

  return Kernel::TermList(v,false);
}

Term FormulaBuilder::term(const Function& f,const Term* args)
{
  CALL("FormulaBuilder::term");

  return _aux->term(f,args,env.signature->functionArity(f));
}

Formula FormulaBuilder::atom(const Predicate& p, const Term* args, bool positive)
{
  CALL("FormulaBuilder::atom");

  return _aux->atom(p,positive, args,env.signature->predicateArity(p));
}

Formula FormulaBuilder::equality(const Term& lhs,const Term& rhs, bool positive)
{
  CALL("FormulaBuilder::equality");

  Literal* lit=Kernel::Literal::createEquality(positive, lhs, rhs);
  return new Kernel::AtomicFormula(lit);
}

Formula FormulaBuilder::trueFormula()
{
  CALL("FormulaBuilder::trueFormula");

  return new Kernel::Formula(Kernel::TRUE);
}

Formula FormulaBuilder::falseFormula()
{
  CALL("FormulaBuilder::falseFormula");

  return new Kernel::Formula(Kernel::FALSE);
}

Formula FormulaBuilder::negation(const Formula& f)
{
  CALL("FormulaBuilder::negation");

  return new Kernel::NegatedFormula(f.form);
}

Formula FormulaBuilder::formula(Connective c,const Formula& f1,const Formula& f2)
{
  CALL("FormulaBuilder::formula");

  Kernel::Connective con;

  switch(c) {
  case AND:
    con=Kernel::AND;
    break;
  case OR:
    con=Kernel::OR;
    break;
  case IMP:
    con=Kernel::IMP;
    break;
  case IFF:
    con=Kernel::IFF;
    break;
  case XOR:
    con=Kernel::XOR;
    break;
  default:
    throw FormulaBuilderException("Invalid binary connective");
  }

  switch(c) {
  case AND:
  case OR:
  {
    Kernel::FormulaList* flst=0;
    Kernel::FormulaList::push(f2.form, flst);
    Kernel::FormulaList::push(f1.form, flst);
    return new Kernel::JunctionFormula(con, flst);
  }
  case IMP:
  case IFF:
  case XOR:
    return new Kernel::BinaryFormula(con, f1.form, f2.form);
  default:
    ASSERTION_VIOLATION;
  }

}

Formula FormulaBuilder::formula(Connective q,const Var& v,const Formula& f)
{
  CALL("FormulaBuilder::formula");

  Kernel::Connective con;

  switch(q) {
  case FORALL:
    con=Kernel::FORALL;
    break;
  case EXISTS:
    con=Kernel::EXISTS;
    break;
  default:
    throw FormulaBuilderException("Invalid quantifier connective");
  }

  Kernel::Formula::VarList* varList=0;
  Kernel::Formula::VarList::push(v, varList);

  return new QuantifiedFormula(con, varList, f.form);
}

//////////////////////////////
// Convenience functions

Term FormulaBuilder::term(const Function& c)
{
  CALL("FormulaBuilder::term/0");

  return _aux->term(c,0,0);
}

Term FormulaBuilder::term(const Function& f,const Term& t)
{
  CALL("FormulaBuilder::term/1");

  return _aux->term(f,&t,1);
}

Term FormulaBuilder::term(const Function& f,const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::term/2");

  Term args[]={t1, t2};
  return _aux->term(f,args,2);
}

Term FormulaBuilder::term(const Function& f,const Term& t1,const Term& t2,const Term& t3)
{
  CALL("FormulaBuilder::term/3");

  Term args[]={t1, t2, t3};
  return _aux->term(f,args,3);
}

Formula FormulaBuilder::formula(const Predicate& p)
{
  CALL("FormulaBuilder::formula/0");

  return _aux->atom(p,true,0,0);
}

Formula FormulaBuilder::formula(const Predicate& p,const Term& t)
{
  CALL("FormulaBuilder::formula/1");

  return _aux->atom(p,true,&t,1);
}

Formula FormulaBuilder::formula(const Predicate& p,const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::formula/2");

  Term args[]={t1, t2};
  return _aux->atom(p,true,args,2);
}

Formula FormulaBuilder::formula(const Predicate& p,const Term& t1,const Term& t2,const Term& t3)
{
  CALL("FormulaBuilder::formula/3");

  Term args[]={t1, t2, t3};
  return _aux->atom(p,true,args,3);
}

AnnotatedFormula FormulaBuilder::annotatedFormula(Formula f, Annotation a)
{
  CALL("FormulaBuilder::annotatedFormula");

  Kernel::Unit::InputType it;
  bool negate=false;
  switch(a) {
  case AXIOM:
    it=Kernel::Unit::AXIOM;
    break;
  case ASSUMPTION:
    it=Kernel::Unit::ASSUMPTION;
    break;
  case LEMMA:
    it=Kernel::Unit::LEMMA;
    break;
  case CONJECTURE:
    it=Kernel::Unit::CONJECTURE;
    negate=true;
    break;
  }

  if(negate) {
    f=negation(Kernel::Formula::quantify(f));
  }

  return new Kernel::FormulaUnit(f, new Kernel::Inference(Kernel::Inference::INPUT), it);
}

//////////////////////////////
// Wrapper implementation

Term::Term(Kernel::TermList t)
{
  content=t.content();
}

Term::operator Kernel::TermList() const
{
  return TermList(content);
}

string Formula::toString() const
{
  CALL("Formula::toString");

  return TPTP::toString(form);
}

string AnnotatedFormula::toString() const
{
  CALL("AnnotatedFormula::toString");

  return TPTP::toString(unit);
}

}

//////////////////////////////
// Output implementation

ostream& operator<< (ostream& str,const Api::Formula& f)
{
  CALL("operator<< (ostream&,const Api::Formula&)");
  return str<<f.toString();
}

ostream& operator<< (ostream& str,const Api::AnnotatedFormula& af)
{
  CALL("operator<< (ostream&,const Api::AnnotatedFormula&)");
  return str<<af.toString();
}


