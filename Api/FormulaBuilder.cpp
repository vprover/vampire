/**
 * @file FormulaBuilder.cpp
 * Implements class FormulaBuilder.
 */

#include "FormulaBuilder.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Map.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/Parser.hpp"
#include "Shell/TPTP.hpp"


using namespace std;
using namespace Lib;
using namespace Shell;

namespace Api
{

typedef Kernel::Formula::VarList VarList;

class DefaultHelperCore
{
public:
  DefaultHelperCore() {}
  virtual ~DefaultHelperCore() {}

  static DefaultHelperCore* instance()
  {
    static DefaultHelperCore inst;

    return &inst;
  }

  virtual string getVarName(Var v) const
  {
    CALL("ApiHelperCore::getVarName");

    return "X"+Int::toString(v);
  }

  string toString(Kernel::TermList t) const
  {
    CALL("DefaultHelperCore::toString(TermList)");

    if(t.isOrdinaryVar()) {
      return getVarName(t.var());
    }
    ASS(t.isTerm());
    return toString(t.term());
  }

  string toString(const Kernel::Term* t0) const
  {
    CALL("DefaultHelperCore::toString(const Kernel::Term*)");

    string res;
    if(t0->isLiteral()) {
      const Literal* l=static_cast<const Literal*>(t0);
      if(l->isEquality()) {
	res=toString(*l->nthArgument(0));
	res+= l->isPositive() ? " = " : " != ";
	res+=toString(*l->nthArgument(1));
	return res;
      }
      res=(l->isPositive() ? "" : "~") + l->predicateName();
    }
    else {
      res=t0->functionName();
    }
    if(t0->arity()==0) {
      return res;
    }

    res+='(';

    static Stack<int> remArg; //how many arguments remain to be printed out for a term at each level
    remArg.reset();
    remArg.push(t0->arity());
    SubtermIterator sti(t0);
    ASS(sti.hasNext());

    while(sti.hasNext()) {
      TermList t=sti.next();
      remArg.top()--;
      ASS_GE(remArg.top(),0);
      bool separated=false;
      if(t.isOrdinaryVar()) {
	res+=getVarName(t.var());
      }
      else {
	Kernel::Term* trm=t.term();
	res+=trm->functionName();
	if(trm->arity()) {
	  res+='(';
	  remArg.push(trm->arity());
	  separated=true;
	}
      }
      if(!separated) {
	while(!remArg.top()) {
	  res+=')';
	  remArg.pop();
	  if(remArg.isEmpty()) {
	    goto fin;
	  }
	}
	ASS(remArg.top());
	res+=',';
      }
    }
    ASSERTION_VIOLATION;

  fin:
    ASS(remArg.isEmpty());
    return res;
  }

  string toString(const Kernel::Formula* f)
  {
    CALL("DefaultHelperCore::toString(const Kernel::Formula*)");

    static string names [] =
      { "", " & ", " | ", " => ", " <=> ", " <~> ",
        "~", "!", "?", "$false", "$true"};
    Connective c = f->connective();
    string con = names[(int)c];
    switch (c) {
    case LITERAL:
      return toString(f->literal());
    case AND:
    case OR:
    {
      const Kernel::FormulaList* fs = f->args();
      string result = "(" + toString(fs->head());
      fs = fs->tail();
      while (! fs->isEmpty()) {
	result += con + toString(fs->head());
	fs = fs->tail();
      }
      return result + ")";
    }

    case IMP:
    case IFF:
    case XOR:
      return string("(") + toString(f->left()) +
             con + toString(f->right()) + ")";

    case NOT:
      return string("(") + con + toString(f->uarg()) + ")";

    case FORALL:
    case EXISTS:
    {
      string result = string("(") + con + "[";
      Kernel::Formula::VarList::Iterator vit(f->vars());
      ASS(vit.hasNext());
      while (vit.hasNext()) {
	result += getVarName(vit.next());
	if(vit.hasNext()) {
	  result += ',';
	}
      }
      return result + "] : (" + toString(f->qarg()) + ") )";
    }
    case FALSE:
    case TRUE:
      return con;
    }
    ASSERTION_VIOLATION;
    return "formula";
  }

  string toString(const Kernel::Clause* clause)
  {
    CALL("DefaultHelperCore::toString(const Kernel::Clause*)");

    string res;
    Kernel::Clause::Iterator lits(*const_cast<Kernel::Clause*>(clause));
    while(lits.hasNext()) {
      res+=toString(lits.next());
      if(lits.hasNext()) {
	res+=" | ";
      }
    }

    if(clause->prop() && !BDD::instance()->isFalse(clause->prop())) {
      if(res!="") {
	res+=" | ";
      }
      res+=BDD::instance()->toTPTPString(clause->prop());
    }
    return res;
  }


  /**
   * Output unit in TPTP format
   *
   * If the unit is a formula of type @b CONJECTURE, output the
   * negation of Vampire's internal representation with the
   * TPTP role conjecture. If it is a clause, just output it as
   * is, with the role negated_conjecture.
   */
  string toString (const Kernel::Unit* unit)
  {
    CALL("DefaultHelperCore::toString(const Kernel::Unit*)");

    string prefix;
    string main = "";

    bool negate_formula = false;
    string kind;
    switch (unit->inputType()) {
    case Unit::ASSUMPTION:
      kind = "hypothesis";
      break;

    case Unit::CONJECTURE:
      if(unit->isClause()) {
	kind = "negated_conjecture";
      }
      else {
	negate_formula = true;
	kind = "conjecture";
      }
      break;

    default:
      kind = "axiom";
      break;
    }

    if (unit->isClause()) {
      prefix = "cnf";
      main = toString(static_cast<const Kernel::Clause*>(unit));
    }
    else {
      prefix = "fof";
      const Kernel::Formula* f = static_cast<const Kernel::FormulaUnit*>(unit)->formula();
      if(negate_formula) {
	Kernel::Formula* quant=Kernel::Formula::quantify(const_cast<Kernel::Formula*>(f));
	if(quant->connective()==NOT) {
	  ASS_EQ(quant,f);
	  main = toString(quant->uarg());
	}
	else {
	  Kernel::Formula* neg=new Kernel::NegatedFormula(quant);
	  main = toString(neg);
	  neg->destroy();
	}
	if(quant!=f) {
	  ASS_EQ(quant->connective(),FORALL);
	  static_cast<Kernel::QuantifiedFormula*>(quant)->vars()->destroy();
	  quant->destroy();
	}
      }
      else {
	main = toString(f);
      }
    }

    string unitName;
    if(!Parser::findAxiomName(unit, unitName)) {
      unitName="u" + Int::toString(unit->number());
    }


    return prefix + "(" + unitName + "," + kind + ",\n"
	+ "    " + main + ").\n";
  }



private:
  struct Var2NameMapper
  {
    Var2NameMapper(DefaultHelperCore& a) : aux(a) {}
    DECL_RETURN_TYPE(string);
    string operator()(Var v)
    {
      return aux.getVarName(v);
    }
    DefaultHelperCore& aux;
  };
public:
  StringIterator getVarNames(VarList* l)
  {
    CALL("ApiHelperCore::getVarNames");

    VirtualIterator<string> res=pvi( getPersistentIterator(
	getMappingIterator(
	    VarList::DestructiveIterator(l),
	    Var2NameMapper(*this))
	) );

    return StringIterator(res);
  }
};

class FBHelperCore
: public DefaultHelperCore
{
public:
  FBHelperCore() : nextVar(0), refCtr(0)
  {
  }

  void incRef()
  {
    CALL("ApiHelperCore::incRef");

    refCtr++;
  }

  /**
   * Decrease the reference counter of the object and destroy it if it
   * becomes zero
   *
   * After the return from this function, the object may not exist any more.
   */
  void decRef()
  {
    CALL("ApiHelperCore::decRef");
    ASS_G(refCtr,0);

    refCtr--;
    if(refCtr==0) {
      delete this;
    }
  }


  /** build a term f(*args) with specified @b arity */
  Term term(const Function& f,const Term* args, unsigned arity)
  {
    CALL("FBHelperCore::term");

    if(f>=static_cast<unsigned>(env.signature->functions())) {
      throw FormulaBuilderException("Function does not exist");
    }
    if(arity!=env.signature->functionArity(f)) {
      throw FormulaBuilderException("Invalid function arity: "+env.signature->functionName(f));
    }

    DArray<TermList> argArr;
    argArr.initFromArray(arity, args);

    Term res(Kernel::TermList(Kernel::Term::create(f,arity,argArr.array())));
    res._aux=this; //assign the correct helper object
    return res;
  }

  /** build a predicate p(*args) with specified @b arity */
  Formula atom(const Predicate& p, bool positive, const Term* args, unsigned arity)
  {
    CALL("FBHelperCore::atom");

    if(p>=static_cast<unsigned>(env.signature->predicates())) {
      throw FormulaBuilderException("Predicate does not exist");
    }
    if(arity!=env.signature->predicateArity(p)) {
      throw FormulaBuilderException("Invalid predicate arity: "+env.signature->predicateName(p));
    }

    DArray<TermList> argArr;
    argArr.initFromArray(arity, args);

    Kernel::Literal* lit=Kernel::Literal::create(p, arity, positive, false, argArr.array());

    Formula res(new Kernel::AtomicFormula(lit));
    res._aux=this; //assign the correct helper object
    return res;
  }

  virtual string getVarName(Var v) const
  {
    CALL("FBHelperCore::getVarName");

    string res;
    if(varNames.find(v,res)) {
      return res;
    }
    else {
      throw FormulaBuilderException("Var object was used in FormulaBuilder object which did not create it");
    }
  }

  Var getVar(string varName)
  {
    if(_checkNames) {
      if(!isupper(varName[0])) {
        throw InvalidTPTPNameException("Variable name must start with an uppercase character", varName);
      }
      //TODO: add further checks
    }

    Var res=vars.insert(varName, nextVar);
    if(res==nextVar) {
      nextVar++;
      varNames.insert(res, varName);
    }
    ASS_L(res, nextVar);
    return res;
  }



  /** indicates whether we shall check names of functions,
   * predicates and variables */
  bool _checkNames;
  /** indicates whether we shall check that we do not bind
   * variables that are already bound in a formula */
  bool _checkBindingBoundVariables;

private:
  /** Map from variable names to their numbers */
  Map<string,Var> vars;
  /** Map from variable names to their numbers */
  Map<Var,string> varNames;
  /** next available variable number */
  Var nextVar;

  int refCtr;
};

ApiHelper::ApiHelper() : _obj(0) {}

ApiHelper::~ApiHelper()
{
  CALL("ApiHelper::~ApiHelper");

  updRef(false);
}

ApiHelper::ApiHelper(const ApiHelper& h)
{
  CALL("ApiHelper::ApiHelper(ApiHelper&)");

  _obj=h._obj;
  updRef(true);
}

ApiHelper& ApiHelper::operator=(const ApiHelper& h)
{
  const_cast<ApiHelper&>(h).updRef(true);
  updRef(false);
  _obj=h._obj;
  return *this;
}

ApiHelper& ApiHelper::operator=(FBHelperCore* hc)
{
  hc->incRef();
  updRef(false);
  _obj=hc;
  return *this;
}

void ApiHelper::updRef(bool inc)
{
  CALL("ApiHelper::updRef");

  if(_obj) {
    if(inc) {
      _obj->incRef();
    }
    else {
      _obj->decRef();
    }
  }
}

bool ApiHelper::operator==(const ApiHelper& h) const
{
  CALL("ApiHelper::operator==");

  return _obj==h._obj;
}

bool ApiHelper::operator!=(const ApiHelper& h) const
{
  CALL("ApiHelper::operator!=");

  return _obj!=h._obj;
}

DefaultHelperCore* ApiHelper::operator->() const
{
  CALL("ApiHelper::operator->");

  if(_obj) {
    return _obj;
  }
  else {
    return DefaultHelperCore::instance();
  }
}

FBHelper::FBHelper()
{
  CALL("FBHelper::FBHelper");

  _obj=new FBHelperCore;
  updRef(true);
}

FBHelperCore* FBHelper::operator->() const
{
  CALL("FBHelper::operator->");

  ASS(_obj);
  return _obj;
}



FormulaBuilder::FormulaBuilder(bool checkNames, bool checkBindingBoundVariables)
{
  CALL("FormulaBuilder::FormulaBuilder");

  _aux->_checkNames=checkNames;
  _aux->_checkBindingBoundVariables=checkBindingBoundVariables;
}

Var FormulaBuilder::var(const string& varName)
{
  CALL("FormulaBuilder::var");

  return _aux->getVar(varName);
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

  Term res(Kernel::TermList(v,false));
  res._aux=_aux; //assign the correct helper object
  return res;
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
  Formula res(new Kernel::AtomicFormula(lit));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::trueFormula()
{
  CALL("FormulaBuilder::trueFormula");

  Formula res(new Kernel::Formula(true));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::falseFormula()
{
  CALL("FormulaBuilder::falseFormula");

  Formula res(new Kernel::Formula(false));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::negation(const Formula& f)
{
  CALL("FormulaBuilder::negation");

  if(f._aux!=_aux) {
    throw FormulaBuilderException("negation function called on a Formula object not built by the same FormulaBuilder object");
  }

  Formula res(new Kernel::NegatedFormula(f.form));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::formula(Connective c,const Formula& f1,const Formula& f2)
{
  CALL("FormulaBuilder::formula(Connective,const Formula&,const Formula&)");

  if(f1._aux!=_aux || f2._aux!=_aux) {
    throw FormulaBuilderException("formula function called on a Formula object not built by the same FormulaBuilder object");
  }

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

  Formula res;
  switch(c) {
  case AND:
  case OR:
  {
    Kernel::FormulaList* flst=0;
    Kernel::FormulaList::push(f2.form, flst);
    Kernel::FormulaList::push(f1.form, flst);
    res=Formula(new Kernel::JunctionFormula(con, flst));
    break;
  }
  case IMP:
  case IFF:
  case XOR:
    res=Formula(new Kernel::BinaryFormula(con, f1.form, f2.form));
    break;
  default:
    ASSERTION_VIOLATION;
  }
  ASS(res.form);
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::formula(Connective q,const Var& v,const Formula& f)
{
  CALL("FormulaBuilder::formula(Connective,const Var&,const Formula&)");

  if(f._aux!=_aux) {
    throw FormulaBuilderException("formula function called on a Formula object not built by the same FormulaBuilder object");
  }
  if(_aux->_checkBindingBoundVariables) {
    VarList* boundVars=static_cast<Kernel::Formula*>(f)->boundVariables();
    bool alreadyBound=boundVars->member(v);
    boundVars->destroy();
    if(alreadyBound) {
      throw FormulaBuilderException("Attempt to bind a variable that is already bound: "+_aux->getVarName(v));
    }
  }

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

  Formula res(new QuantifiedFormula(con, varList, f.form));
  res._aux=_aux; //assign the correct helper object
  return res;
}

AnnotatedFormula FormulaBuilder::annotatedFormula(Formula f, Annotation a, string name)
{
  CALL("FormulaBuilder::annotatedFormula");

  if(f._aux!=_aux) {
    throw FormulaBuilderException("annotatedFormula function called on a Formula object not built by the same FormulaBuilder object");
  }

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
    Formula inner(Kernel::Formula::quantify(f));
    inner._aux=_aux;
    f=negation(inner);
  }

  FormulaUnit* fures=new Kernel::FormulaUnit(f, new Kernel::Inference(Kernel::Inference::INPUT), it);

  if(name!="") {
    Parser::assignAxiomName(fures, name);
  }

  AnnotatedFormula res(fures);
  res._aux=_aux; //assign the correct helper object
  return res;
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


//////////////////////////////
// Wrapper implementation

Term::Term(Kernel::TermList t)
{
  content=t.content();
}

string Term::toString() const
{
  CALL("Term::toString");

  return _aux->toString(static_cast<Kernel::TermList>(*this));
}

Term::operator Kernel::TermList() const
{
  return TermList(content);
}

string Formula::toString() const
{
  CALL("Formula::toString");

  return _aux->toString(static_cast<Kernel::Formula*>(*this));
}

bool Formula::isTrue() const
{ return form->connective()==Kernel::TRUE; }

bool Formula::isFalse() const
{ return form->connective()==Kernel::FALSE; }

bool Formula::isNegation() const
{ return form->connective()==Kernel::NOT; }

StringIterator Formula::freeVars()
{
  CALL("Formula::freeVars");

  if(!form) {
    return StringIterator(VirtualIterator<string>::getEmpty());
  }
  VarList* vars=form->freeVariables();
  return _aux->getVarNames(vars);
}

StringIterator Formula::boundVars()
{
  CALL("Formula::boundVars");

  if(!form) {
    return StringIterator(VirtualIterator<string>::getEmpty());
  }
  VarList* vars=form->boundVariables();
  return _aux->getVarNames(vars);
}


string AnnotatedFormula::toString() const
{
  CALL("AnnotatedFormula::toString");

  return _aux->toString(unit);
}

string AnnotatedFormula::name() const
{
  CALL("AnnotatedFormula::toString");

  string unitName;
  if(!Parser::findAxiomName(unit, unitName)) {
    unitName="u" + Int::toString(unit->number());
  }
  return unitName;
}

StringIterator AnnotatedFormula::freeVars()
{
  CALL("AnnotatedFormula::freeVars");

  if(!unit) {
    return StringIterator(VirtualIterator<string>::getEmpty());
  }
  VarList* vl=0;
  if(unit->isClause()) {
    VarList::pushFromIterator(static_cast<Clause*>(unit)->getVariableIterator(), vl);
  }
  else {
    vl=static_cast<FormulaUnit*>(unit)->formula()->freeVariables();
  }
  return _aux->getVarNames(vl);
}

StringIterator AnnotatedFormula::boundVars()
{
  CALL("AnnotatedFormula::boundVars");

  if(!unit || unit->isClause()) {
    return StringIterator(VirtualIterator<string>::getEmpty());
  }
  VarList* vl=static_cast<FormulaUnit*>(unit)->formula()->boundVariables();
  return _aux->getVarNames(vl);
}


//////////////////////////////
// StringIterator implementation

StringIterator::StringIterator(const VirtualIterator<string>& vit)
{
  CALL("StringIterator::StringIterator");

  _impl=new VirtualIterator<string>(vit);
}

StringIterator::~StringIterator()
{
  CALL("StringIterator::~StringIterator");

  if(_impl) {
    delete _impl;
  }
}

StringIterator::StringIterator(const StringIterator& it)
{
  CALL("StringIterator::StringIterator(StringIterator&)");

  if(it._impl) {
    _impl=new VirtualIterator<string>(*it._impl);
  }
  else {
    _impl=0;
  }
}

StringIterator& StringIterator::operator=(const StringIterator& it)
{
  CALL("StringIterator::operator=");

  VirtualIterator<string>* oldImpl=_impl;

  if(it._impl) {
    _impl=new VirtualIterator<string>(*it._impl);
  }
  else {
    _impl=0;
  }

  if(oldImpl) {
    delete oldImpl;
  }

  return *this;
}

bool StringIterator::hasNext()
{
  CALL("StringIterator::hasNext");

  if(!_impl) {
    return false;
  }

  return _impl->hasNext();
}

string StringIterator::next()
{
  CALL("StringIterator::next");

  if(!hasNext()) {
    throw FormulaBuilderException("next() function called on a StringIterator object that contains no more elements");
  }
  ASS(_impl);
  return _impl->next();
}

} //namespace Api


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

