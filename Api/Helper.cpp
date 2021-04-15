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
 * @file Helper.cpp
 * Implements class Helper.
 */

#include "Kernel/SortHelper.hpp"

#include "Parse/TPTP.hpp"

#include "Helper_Internal.hpp"

namespace Api
{

using namespace Kernel;
using namespace Shell;

///////////////////////
// DefaultHelperCore
//


DefaultHelperCore* DefaultHelperCore::instance()
{
  static DefaultHelperCore inst;

  return &inst;
}

vstring DefaultHelperCore::getVarName(Var v) const
{
  CALL("DefaultHelperCore::getVarName");

  return "X"+Int::toString(v);
}

vstring DefaultHelperCore::toString(Kernel::TermList t) const
{
  CALL("DefaultHelperCore::toString(TermList)");

  if(t.isOrdinaryVar()) {
    return getVarName(t.var());
  }
  ASS(t.isTerm());
  return toString(t.term());
}

/** Get dummy name for function or predicate */
vstring DefaultHelperCore::getDummyName(bool pred, unsigned functor)
{
  CALL("DefaultHelperCore::getDummyName/2");

  Signature::Symbol* sym = pred ?
      env.signature->getPredicate(functor) :
      env.signature->getFunction(functor);

  if(sym->interpreted()) {
    return pred ? env.signature->predicateName(functor) :
	env.signature->functionName(functor);
  }

  if(pred) {
    return "p"+Int::toString(functor);
  }
  else {
    return "f"+Int::toString(functor);
  }
}

/** Get dummy name for function or predicate */
vstring DefaultHelperCore::getDummyName(const Kernel::Term* t)
{
  CALL("DefaultHelperCore::getDummyName/1");

  return getDummyName(t->isLiteral(), t->functor());
}

vstring DefaultHelperCore::getSymbolName(bool pred, unsigned functor) const
{
  if(outputDummyNames()) {
    return getDummyName(pred, functor);
  }
  else {
    if(pred) {
      return env.signature->predicateName(functor);
    }
    else {
      return env.signature->functionName(functor);
    }
  }
}

vstring DefaultHelperCore::getSymbolName(const Kernel::Term* t) const
{
  return getSymbolName(t->isLiteral(), t->functor());
}


vstring DefaultHelperCore::toString(const Kernel::Term* t0) const
{
  CALL("DefaultHelperCore::toString(const Kernel::Term*)");

  vstring res;
  if(t0->isSpecial()) {
    return t0->specialTermToString();
  }


  if(t0->isLiteral()) {
    const Literal* l=static_cast<const Literal*>(t0);
    if(l->isEquality()) {
      if(OutputOptions::sortedEquality()) {
	unsigned sort = SortHelper::getEqualityArgumentSort(l);
	res=(l->isPositive() ? "" : "~");
	res+="$$equality_sorted(";
	res+=env.sorts->sortName(sort)+",";
	res+=toString(*l->nthArgument(0))+",";
	res+=toString(*l->nthArgument(1))+")";
	return res;
      }
      else {
	res=toString(*l->nthArgument(0));
	res+= l->isPositive() ? " = " : " != ";
	res+=toString(*l->nthArgument(1));
	return res;
      }
    }
    res=(l->isPositive() ? "" : "~") + getSymbolName(l);
  }
  else {
    res=getSymbolName(t0);
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
      if(trm->isSpecial()) {
	//we handle special terms at the top level
	res+=toString(trm);
      }
      else {
	res+=getSymbolName(trm);
	if(trm->arity()) {
	  res+='(';
	  remArg.push(trm->arity());
	  separated=true;
	}
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

vstring DefaultHelperCore::toString(const Kernel::Formula* f0) const
{
  CALL("DefaultHelperCore::toString(const Kernel::Formula*)");

  Kernel::Formula* f = const_cast<Kernel::Formula*>(f0);

  static vstring names [] =
  { "", " & ", " | ", " => ", " <=> ", " <~> ",
      "~", "!", "?", "$term", "$false", "$true"};
  ASS_EQ(sizeof(names)/sizeof(vstring), TRUE+1);
  Connective c = f->connective();
  vstring con = names[(int)c];
  switch (c) {
  case LITERAL:
    return toString(f->literal());
  case AND:
  case OR:
  {
    const Kernel::FormulaList* fs = f->args();
    vstring result = "(" + toString(fs->head());
    fs = fs->tail();
    while (Kernel::FormulaList::isNonEmpty(fs)) {
      result += con + toString(fs->head());
      fs = fs->tail();
    }
    return result + ")";
  }

  case IMP:
  case IFF:
  case XOR:
    return vstring("(") + toString(f->left()) +
	con + toString(f->right()) + ")";

  case NOT:
    return vstring("(") + con + toString(f->uarg()) + ")";

  case FORALL:
  case EXISTS:
  {
    vstring result = vstring("(") + con + "[";
    VList::Iterator vit(f->vars());
    ASS(vit.hasNext());
    while (vit.hasNext()) {
      unsigned var = vit.next();
      result += getVarName(var);
      if(OutputOptions::tffFormulas()) {
	result += " : ";
	unsigned sort;
	if(isFBHelper()) {
	  Sort srt = static_cast<const FBHelperCore*>(this)->getVarSort(var);
	  if(srt.isValid()) {
	    sort = srt;
	  }
	  else if(!SortHelper::tryGetVariableSort(var, f->qarg(), sort)) {
	    sort = Sorts::SRT_DEFAULT;
	  }
	}
	else {
	  if(!SortHelper::tryGetVariableSort(var, f->qarg(), sort)) {
	    sort = Sorts::SRT_DEFAULT;
	  }
	}
	result += env.sorts->sortName(sort);
      }
      if(vit.hasNext()) {
	result += ',';
      }
    }
    return result + "] : (" + toString(f->qarg()) + ") )";
  }

  case BOOL_TERM:
    return f->getBooleanTerm().toString();

  case FALSE:
  case TRUE:
    return con;
  }
  ASSERTION_VIOLATION;
  return "formula";
}

vstring DefaultHelperCore::toString(const Kernel::Clause* clause) const
{
  CALL("DefaultHelperCore::toString(const Kernel::Clause*)");

  vstring res;
  Kernel::Clause::Iterator lits(*const_cast<Kernel::Clause*>(clause));
  if(lits.hasNext()) {
    while(lits.hasNext()) {
      res+=toString(lits.next());
      if(lits.hasNext()) {
	res+=" | ";
      }
    }
  }
  else {
    res += "$false";
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
vstring DefaultHelperCore::toString (const Kernel::Unit* unit0) const
{
  CALL("DefaultHelperCore::toString(const Kernel::Unit*)");

  Kernel::Unit* unit = const_cast<Kernel::Unit*>(unit0);
  vstring prefix;
  vstring main = "";

  bool negate_formula = false;
  vstring kind;
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

  vstring unitName;
  if(!Parse::TPTP::findAxiomName(unit, unitName)) {
    unitName="u" + Int::toString(unit->number());
  }

  if (unit->isClause()) {
    if(OutputOptions::tffFormulas()) {
      prefix = "tff";
      //we convert clause into a formula in order to print the
      //variables quantified with types
      Kernel::Formula* f = Kernel::Formula::fromClause(const_cast<Kernel::Clause*>(static_cast<const Kernel::Clause*>(unit)));
      main = toString(f);
      //here we have a memory leak (of f), but we probably don't worry about it
    }
    else {
      prefix = "cnf";
      main = toString(static_cast<const Kernel::Clause*>(unit));
    }
  }
  else {
    prefix = OutputOptions::tffFormulas() ? "tff" : "fof";
    const Kernel::Formula* f0 = static_cast<const Kernel::FormulaUnit*>(unit)->formula();
    Kernel::Formula* f = const_cast<Kernel::Formula*>(f0);
    f=Kernel::Formula::quantify(f);
    if(negate_formula) {
      if(f->connective()==NOT) {
	ASS_EQ(f,f0);
	main = toString(f->uarg());
      }
      else {
	Kernel::Formula* neg=new Kernel::NegatedFormula(f);
	main = toString(neg);
	neg->destroy();
      }
    }
    else {
      main = toString(f);
    }
    if(f0!=f) {
      ASS_EQ(f->connective(),FORALL);
      ASS_EQ(f->qarg(),f0);
      static_cast<Kernel::QuantifiedFormula*>(f)->vars()->destroy();
      f->destroy();
    }
  }



  return prefix + "(" + unitName + "," + kind + ",\n"
      + "    " + main + ").\n";
}

struct DefaultHelperCore::Var2NameMapper
{
  Var2NameMapper(DefaultHelperCore& a) : aux(a) {}
  vstring operator()(unsigned v)
  {
    return aux.getVarName(v);
  }
  DefaultHelperCore& aux;
};

StringIterator DefaultHelperCore::getVarNames(VList* l)
{
  CALL("DefaultHelperCore::getVarNames");

  VirtualIterator<vstring> res=pvi( getPersistentIterator(
      getMappingIterator(
	  VList::DestructiveIterator(l),
	  Var2NameMapper(*this))
  ) );

  return StringIterator(res);
}



///////////////////////
// FBHelperCore
//


/** build a term f(*args) with specified @b arity */
Term FBHelperCore::term(const Function& f,const Term* args, unsigned arity)
{
  CALL("FBHelperCore::term");

  if(f>=static_cast<unsigned>(env.signature->functions())) {
    throw FormulaBuilderException("Function does not exist");
  }
  if(arity!=env.signature->functionArity(f)) {
    throw FormulaBuilderException("Invalid function arity: "+env.signature->functionName(f));
  }
  ensureArgumentsSortsMatch(env.signature->getFunction(f)->fnType(), args);

  DArray<TermList> argArr;
  argArr.initFromArray(arity, args);

  Term res(Kernel::TermList(Kernel::Term::create(f,arity,argArr.array())));
  res._aux=this; //assign the correct helper object
  return res;
}

/** build a predicate p(*args) with specified @b arity */
Formula FBHelperCore::atom(const Predicate& p, bool positive, const Term* args, unsigned arity)
{
  CALL("FBHelperCore::atom");

  if(p>=static_cast<unsigned>(env.signature->predicates())) {
    throw FormulaBuilderException("Predicate does not exist");
  }
  if(arity!=env.signature->predicateArity(p)) {
    throw FormulaBuilderException("Invalid predicate arity: "+env.signature->predicateName(p));
  }
  ensureArgumentsSortsMatch(env.signature->getPredicate(p)->predType(), args);

  DArray<TermList> argArr;
  argArr.initFromArray(arity, args);

  Kernel::Literal* lit=Kernel::Literal::create(p, arity, positive, false, argArr.array());

  Formula res(new Kernel::AtomicFormula(lit));
  res._aux=this; //assign the correct helper object
  return res;
}

unsigned FBHelperCore::getUnaryPredicate()
{
  CALL("FBHelperCore::getUnaryPredicate");

  if(_unaryPredicate!=0) {
    return _unaryPredicate;
  }

  Kernel::Signature& sig = *env.signature;
  unsigned cnt = sig.predicates();
  for(unsigned i=1; i<cnt; i++) {
    if(sig.predicateArity(i)==1 && !sig.getPredicate(i)->interpreted()) {
      _unaryPredicate = i;
      return i;
    }
  }
  _unaryPredicate = sig.addNamePredicate(1);
  return _unaryPredicate;
}

Sort FBHelperCore::getSort(const Api::Term t)
{
  CALL("FBHelperCore::getSort");

  if(t.isVar()) {
    unsigned v = t.var();
    return getVarSort(v);
  }
  else {
    unsigned fun = t.functor();
    return Sort(env.signature->getFunction(fun)->fnType()->result());
  }
}

void FBHelperCore::ensureArgumentsSortsMatch(BaseType* type, const Api::Term* args)
{
  CALL("FBHelperCore::ensureArgumentsSortsMatch");

  unsigned arity = type->arity();
  for(unsigned i=0; i<arity; i++) {
    unsigned parentSort = type->arg(i);
    Sort argSort = getSort(args[i]);
    if(argSort.isValid() && parentSort!=argSort) {
      throw SortMismatchException("Unexpected sort of term " + args[i].toString());
    }
  }
}

void FBHelperCore::ensureEqualityArgumentsSortsMatch(const Api::Term arg1, const Api::Term arg2)
{
  CALL("FBHelperCore::ensureEqualityArgumentsSortsMatch");

  Sort s1 = getSort(arg1);
  Sort s2 = getSort(arg2);  
  if(s1!=s2) {
    throw SortMismatchException("Different sorts of equality arguments: " + arg1.toString() + " and " + arg2.toString());
  }
}

vstring FBHelperCore::getVarName(Var v) const
{
  CALL("FBHelperCore::getVarName");

  if(outputDummyNames()) {
    return "X"+Int::toString(v);
  }

  vstring res;
  if(varNames.find(v,res)) {
    return res;
  }
  else {
    static bool seen = false;
    if(!seen) {
      seen = true;      
    }
    return "X"+Int::toString(v);

//    Map<Var,vstring>::Iterator it(varNames);
//    while(it.hasNext()) {
//      vstring v;
//      unsigned k;
//      it.next(k,v);
//      cout<<k<<" "<<v<<endl;
//    }
//    throw FormulaBuilderException("Var object was used in FormulaBuilder object which did not create it");
  }
}

Sort FBHelperCore::getVarSort(Var v) const
{
  CALL("FBHelperCore::getVarSort");

  Sort res;
  if(varSorts.find(v,res)) {
    return res;
  }
  else {   
    return Sort::getInvalid();
//    throw FormulaBuilderException("Var object was used in FormulaBuilder object which did not create it");
  }
}

unsigned FBHelperCore::getVar(vstring varName, Sort varSort)
{
  if(_checkNames) {
    if(!isupper(varName[0])) {
      throw InvalidTPTPNameException("Variable name must start with an uppercase character", varName);
    }
    //TODO: add further checks
  }
  
  unsigned res=vars.insert(varName, nextVar);
  if(res==nextVar) {
    nextVar++;
    varNames.insert(res, varName);
    varSorts.insert(res, varSort);
  }
  else {
    Sort oldSort = varSorts.get(res);
    if(!oldSort.isValid()) {
      if(varSort.isValid()) {
	varSorts.replace(res, varSort);
      }
    }
    else {
      if(varSort.isValid() && oldSort!=varSort) {
	throw FormulaBuilderException("Existing variable with different sort requested");
      }
    }
  }
  ASS_L(res, nextVar);
  return res;
}

void FBHelperCore::addAttribute(AttribStack& stack, vstring name, vstring value)
{
  CALL("FBHelperCore::addAttribute");

  AttribPair attr(name,value);
  //TODO: This causes quadratic complexity in the number of attributes
  if(stack.find(attr)) {
    return;
  }
  stack.push(attr);
}


/**
 * Return an alias variable for variable number @b var
 */
unsigned FBHelperCore::FBVarFactory::getVarAlias(unsigned var)
{
  CALL("FBHelperCore::FBVarFactory::getVarAlias");

  vstring origName=_parent.getVarName(var);
  int i=0;
  vstring name;
  do {
    i++;
    name=origName+"_"+Int::toString(i);
  } while(_parent.vars.find(name));

  return _parent.getVar(name, _parent.getVarSort(var));
}

/**
 * Return name of variable number @b var
 */
vstring FBHelperCore::FBVarFactory::getVarName(unsigned var)
{
  CALL("FBHelperCore::FBVarFactory::getVarName");

  return _parent.getVarName(var);
}


///////////////////////
// ApiHelper
//

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

  return **this;
}

DefaultHelperCore* ApiHelper::operator*() const
{
  CALL("ApiHelper::operator*");

  if(_obj) {
    return _obj;
  }
  else {
    return DefaultHelperCore::instance();
  }
}

///////////////////////
// FBHelper
//


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


}
