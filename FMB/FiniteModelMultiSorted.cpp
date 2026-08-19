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
 * @file FiniteModelMultiSorted.cpp
 * Defines class for finite models
 *
 * @since 7/01/2016 Manchester
 * @author Giles
 */

#include <climits>

#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Lib/Environment.hpp"
#include "Lib/DHMap.hpp"

#include "Shell/Rectify.hpp"
#include "Shell/SimplifyFalseTrue.hpp"
#include "Shell/Flattening.hpp"

#include "ArgsEnumerator.hpp"
#include "FiniteModelMultiSorted.hpp"

#define DEBUG_MODEL 0

namespace FMB{

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

// the extent of sort s under the domain sizes sizes;
// a sort with no domain in this model (size 0 -- see the comment on _sizes) behaves as a
// singleton wherever a value of it is nevertheless called for, which is also what
// ArgsEnumerator does with a 0 bound (its do/while runs the first tuple in any case)
static unsigned domainSize(const DArray<unsigned>& sizes, unsigned s)
{
  unsigned size = sizes[s];
  return size > 0 ? size : 1;
}

// captures the encoding of a symbol's table:
// the row index of the tuple args in the table of a symbol of type sig,
// under the domain sizes sizes -- the first argument position changing fastest,
// i.e. the very order in which ArgsEnumerator enumerates the tuples
static size_t tableIndex(const DArray<unsigned>& args, const DArray<unsigned>& sizes, OperatorType* sig)
{
  size_t idx = 0;
  size_t mult = 1;
  for(unsigned i=0;i<args.size();i++){
    idx += mult*(args[i]-1);
    unsigned s = sig->arg(i).term()->functor();
    unsigned dim = domainSize(sizes,s);
    ASS_G(args[i],0); ASS_LE(args[i],dim); // domain elements are 1-based and inside their sort
    mult *= dim;
  }
  return idx;
}

// computes the number of rows of the table of a symbol of type sig under the domain sizes sizes
static size_t tableSize(OperatorType* sig, unsigned arity, const DArray<unsigned>& sizes)
{
  size_t size = 1;
  for(unsigned i=0;i<arity;i++) {
    unsigned mult = domainSize(sizes,sig->arg(i).term()->functor());
    if (mult > 1 && size > SIZE_MAX / mult) {
      INVALID_OPERATION("Model too large to represent!");
    }
    size *= mult;
  }
  return size;
}

void FiniteModelMultiSorted::initTables()
{
  _f_tables.ensure(env.signature->functions());
  _p_tables.ensure(env.signature->predicates());

  for(unsigned f=0; f<env.signature->functions();f++){
    Signature::Symbol* symb = env.signature->getFunction(f);
    if (symb->usageCnt()==0) {
      // the SAT solver skipped some functions as they are eliminated
      // (the model, on the other hand, should be prepared to give them values later)
      _f_tables[f] = DArray<unsigned>(); // not represented
      continue;
    }

    DArray<unsigned> tbl;
    tbl.expand(tableSize(symb->fnType(),symb->arity(),_sizes),0);
    _f_tables[f] = std::move(tbl);
  }

  _p_tables[0] = DArray<char>(); // equality is never tabulated
  for(unsigned p=1; p<env.signature->predicates();p++){
    Signature::Symbol* symb = env.signature->getPredicate(p);
    if (symb->usageCnt()==0) {
      _p_tables[p] = DArray<char>(); // not represented
      continue;
    }

    DArray<char> tbl;
    tbl.expand(tableSize(symb->predType(),symb->arity(),_sizes),0);
    _p_tables[p] = std::move(tbl);
  }
}

Problem::FunDef* FiniteModelMultiSorted::symbolicFunDef(unsigned f)
{
  Problem::FunDef* fd;
  if (!_symbolicFuns.find(f,fd)) {
    // implicitly eliminated symbol (its last occurrence disappeared with some other elimination),
    // so it can be defined arbitrarily: record a trivial definition --
    // a linear head f(X0,...,X_{arity-1}) and a null body standing for "the first domain element"
    TermStack args;
    for (unsigned v = 0; v < env.signature->functionArity(f); v++) {
      args.push(TermList::var(v));
    }
    fd = new Problem::FunDef(Term::create(f,args.size(),args.begin()),nullptr /* arbitrary value */);
    _symbolicFuns.insert(f,fd);
  }
  return fd;
}

Problem::PredDef* FiniteModelMultiSorted::symbolicPredDef(unsigned p)
{
  Problem::PredDef* pd;
  if (!_symbolicPreds.find(p,pd)) {
    // implicitly eliminated symbol; record the trivial definition p(X0,...,X_{arity-1}) <=> $false
    TermStack args;
    for (unsigned v = 0; v < env.signature->predicateArity(p); v++) {
      args.push(TermList::var(v));
    }
    pd = new Problem::PredDef(Literal::create(p, args.size(), true, args.begin()),new Formula(false));
    _symbolicPreds.insert(p,pd);
  }
  return pd;
}

void FiniteModelMultiSorted::addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res)
{
  ASS_EQ(env.signature->functionArity(f),args.size());

  OperatorType* tp = env.signature->getFunction(f)->fnType();
  // a function's value must be a domain element of its result sort
  ASS_G(res,0); ASS_LE(res,domainSize(_sizes,tp->result().term()->functor()));

  DArray<unsigned>& tbl = _f_tables[f];
  size_t idx = tableIndex(args,_sizes,tp);

  ASS_L(idx, tbl.size());
  tbl[idx] = res;
}

void FiniteModelMultiSorted::addPredicateDefinition(unsigned p, const DArray<unsigned>& args, bool res)
{
  ASS_EQ(env.signature->predicateArity(p),args.size());

  DArray<char>& tbl = _p_tables[p];
  size_t idx = tableIndex(args,_sizes,env.signature->getPredicate(p)->predType());

  ASS_L(idx, tbl.size());
  tbl[idx] = (res ? INTP_TRUE : INTP_FALSE);
}

std::string FiniteModelMultiSorted::toString()
{
  std::ostringstream modelStm;

  bool printIntroduced = false;

  static DArray<DArray<std::string>> cnames;
  cnames.ensure(env.signature->typeCons());

  //Output sorts and their sizes
  for(unsigned s=0;s<env.signature->typeCons();s++){
    unsigned size = _sizes[s];
    if(size==0) continue;

    // don't output interpreted sorts at all, we know what they are
    // ($o is the exception: FMB models it like any other sort -- FOOL elimination and
    // TheoryAxioms::applyFOOL turn the booleans into ordinary terms and axioms -- only its
    // two domain elements are built-in and already named, see below)
    if(env.signature->isInterpretedNonDefault(s) && !env.signature->isBoolCon(s))
      continue;

    std::string sortName = env.signature->typeConName(s);
    std::string sortNameLabel = (env.signature->isBoolCon(s)) ? "bool" : sortName;

    // skip declaring $i and $o, we know what they are
    if(!env.signature->isDefaultSortCon(s))
      // Sort declaration
      modelStm << "tff(" << prepend("declare_", sortNameLabel) << ",type,"<<sortName<<":$tType)." <<endl;

    cnames[s].ensure(size+1);

    if(env.signature->isBoolCon(s)){
      // The two boolean domain elements are FOOL's term-level booleans, printed as $true and
      // $false (or, under -show_fool on, as the internal $$true / $$false -- which the parser
      // does not accept in term position, so such a model is for reading only).
      // Which element is which is what this model says about the two constants; there are no
      // type declarations to emit for them, they are built-in.
      ASS_EQ(size,2);
      ASS(env.signature->foolConstantsDefined());
      for (unsigned i = 0; i < 2; i++) {
        bool isTrue = (i > 0);
        cnames[s][boolValue(isTrue)] =
          env.signature->functionName(env.signature->getFoolConstantSymbol(isTrue));
      }
      ASS_NEQ(cnames[s][1],cnames[s][2]);
    } else {
      // Domain constant declarations
      for(unsigned i=1;i<=size;i++){
        modelStm << "tff(" << append(prepend("declare_", sortNameLabel), Int::toString(i).c_str()) << ",type,";
        std::string cname = append(prepend("fmb_", sortNameLabel),(std::string("_")+Lib::Int::toString(i)).c_str());
        cnames[s][i]=cname;
        modelStm << cname << ":" << sortName << ")." << endl;
      }
    }

    //Output domain
    modelStm << "tff(" << prepend("finite_domain_", sortNameLabel) << ",axiom," << endl;
    modelStm << "      ! [X:" << sortName << "] : (" << endl;
    modelStm << "         ";
    for(unsigned i=1;i<=size;i++){
      // the parentheses matter for $o: our own parser reads an unbracketed
      // "X = $false | X = $true" as "X = ($false | X = $true)"
      modelStm << "(X = " << cnames[s][i] << ")";
      if(i<size) modelStm << " | ";
      if(i==size) modelStm << endl;
      else if(i%5==0) modelStm << endl << "         ";
    }
    modelStm << "      ) )." <<endl;
    //Distinctness of domain
    modelStm << endl;
    if(size>1){
    modelStm << "tff(" << prepend("distinct_domain_", sortNameLabel) << ",axiom," << endl;
    modelStm << "         ";
    unsigned c=0;
    for(unsigned i=1;i<=size;i++){
      for(unsigned j=i+1;j<=size;j++){
        c++;
        modelStm << cnames[s][i] <<" != " << cnames[s][j];
        if(!(i==size-1 && j==size)){
           modelStm << " & ";
           if(c%5==0){ modelStm << endl << "         "; }
        }
        else{ modelStm << endl; }
      }
    }
    modelStm << ")." << endl << endl;
    }
  }

  // Functions (including constants)
  for(unsigned f=0;f<env.signature->functions();f++){
    Signature::Symbol* symb = env.signature->getFunction(f);
    unsigned arity = symb->arity();
    if(!printIntroduced && symb->introduced()) continue;
    // the boolean domain elements are named after these two, so their definitions
    // would just be the tautologies $true = $true and $false = $false
    if(env.signature->isFoolConstantSymbol(true,f) || env.signature->isFoolConstantSymbol(false,f)) continue;
    std::string name = symb->name();

    OperatorType* ot = symb->fnType();
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<" : ";
    if (arity>0) {
      modelStm << "( ";
      for(unsigned i=0;i<arity;i++){
        modelStm << ot->arg(i).toString();
        if(i+1 < arity) modelStm << " * ";
      }
      modelStm << " ) > ";
    }
    modelStm << ot->result().toString() << ")." << endl;

    if (!funRepresented(f)) {
      Problem::FunDef* fd = symbolicFunDef(f);

      // print a symbolic definition (the explicit one was missing)

      modelStm << "tff("<<append(name,"_symbolic_definition")<<",axiom,";
      if (arity>0) { // quantify
        modelStm << "![";
        for(unsigned i=0;i<arity;i++){
          modelStm << fd->_head->nthArgument(i)->toString();
          modelStm << ":" << ot->arg(i).toString();
          if(i+1 < arity) modelStm << ", ";
        }
        modelStm << "]: ";
      }
      modelStm << fd->_head->toString() << " = ";
      if (fd->_body) {
        modelStm << fd->_body->toString();
      } else {
        TermList srtT = ot->result();
        unsigned srt = srtT.term()->functor();
        std::string cname = cnames[srt][1]; // using 1 as an abitrary value
        modelStm << cname;
      }

      modelStm << ")." <<endl;
      continue;
    }

    if (arity == 0) {
      unsigned res = _f_tables[f][0];
      ASS_G(res,0)

      TermList srtT = ot->result();
      unsigned srt = srtT.term()->functor();
      std::string cname = cnames[srt][res];

      modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<<" = " << cname << ")."<<endl;
    } else {
      modelStm << "tff("<<prepend("function_", name)<<",axiom,"<<endl;

      bool first=true;
      const DArray<unsigned>& tbl = _f_tables[f];
      size_t idx = 0; // the enumeration visits the table rows in order
      ArgsEnumerator it(_sizes,ot,arity);
      do {
        const DArray<unsigned>& args = it.args();
        ASS_EQ(idx,tableIndex(args,_sizes,ot));
        unsigned res = tbl[idx++];
        ASS_G(res,0)

        if (!first) {
          modelStm << "         & ";
        } else {
          modelStm << "           ";
        }
        first=false;
        modelStm << name << "(";
        for(unsigned j=0;j<arity;j++){
          if(j!=0) modelStm << ",";
          TermList argSortT = ot->arg(j);
          unsigned argSort = argSortT.term()->functor();
          modelStm << cnames[argSort][args[j]];
        }
        TermList resultSortT = ot->result();
        unsigned resultSort = resultSortT.term()->functor();
        modelStm << ") = " << cnames[resultSort][res] << endl;
      } while (it.next());
      ASS_EQ(idx,tbl.size());
      modelStm << ")." << endl << endl;
    }
  }

  //Predicates (including propositions)
  for(unsigned p=1;p<env.signature->predicates();p++){
    Signature::Symbol* symb = env.signature->getPredicate(p);
    unsigned arity = symb->arity();
    if(!printIntroduced && symb->introduced()) continue;
    std::string name = symb->name();
    OperatorType* ot = symb->predType();
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<": "; //"(";
    if (arity>0) {
      modelStm << "( ";
      for(unsigned i=0;i<arity;i++){
        TermList argST = ot->arg(i);
        unsigned argS = argST.term()->functor();
        modelStm << env.signature->typeConName(argS);
        if(i+1 < arity) modelStm << " * ";
      }
      modelStm << " ) > ";
    }
    modelStm << "$o )." << endl;

    if (!predRepresented(p)) {
      Problem::PredDef* pd = symbolicPredDef(p);

      // print a symbolic definition (the explicit one was missing)

      modelStm << "tff("<<append(name,"_symbolic_definition")<<",axiom,";
      if (arity>0) { // quantify
        modelStm << "![";
        for(unsigned i=0;i<arity;i++){
          modelStm << pd->_head->nthArgument(i)->toString();
          modelStm << ":" << ot->arg(i).toString();
          if(i+1 < arity) modelStm << ", ";
        }
        modelStm << "]: (";
      }
      modelStm << pd->_head->toString() << " <=> " << pd->_body->toString();
      if (arity>0)
        modelStm << ")";
      modelStm << ")." <<endl;

      continue;
    }

    if (arity==0) {
      char res = _p_tables[p][0];
      if(res==INTP_TRUE){
        modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<< ")."<<endl;
      } else { // covers (res==INTP_FALSE) as well as undefined, which defaults to false
        modelStm << "tff("<<append(name,"_definition")<<",axiom,~"<<name<< ")."<<endl;
      }
    } else {
      modelStm << "tff("<<prepend("predicate_", name)<<",axiom,"<<endl;

      bool first=true;
      const DArray<char>& tbl = _p_tables[p];
      size_t idx = 0; // the enumeration visits the table rows in order
      ArgsEnumerator it(_sizes,ot,arity);
      do {
        const DArray<unsigned>& args = it.args();
        ASS_EQ(idx,tableIndex(args,_sizes,ot));
        char res = tbl[idx++];
        ASS_NEQ(res,INTP_UNDEF)

        if (!first){
          modelStm << "         & ";
        } else {
          modelStm << "           ";
        }
        first=false;

        if(res==INTP_FALSE) modelStm << "~";
        modelStm << name << "(";
        for(unsigned j=0;j<arity;j++){
          if(j!=0) modelStm << ",";
          TermList argSortT = ot->arg(j);
          unsigned argSort = argSortT.term()->functor();
          modelStm << cnames[argSort][args[j]];
        }
        modelStm << ")";
        modelStm << endl;
      } while (it.next());
      ASS_EQ(idx,tbl.size());
      modelStm << ")." << endl << endl;
    }
  }

  return modelStm.str();
}

TermList FiniteModelMultiSorted::deFool(TermList tl)
{
  if (tl.isTerm() && tl.term()->isSpecial() &&
      tl.term()->specialFunctor() == SpecialFunctor::FORMULA) {
    Connective con = tl.term()->getSpecialData()->getFormula()->connective();
    if (con == TRUE || con == FALSE) {
      return TermList(Term::createConstant(env.signature->getFoolConstantSymbol(con == TRUE)));
    }
  }
  return tl;
}

unsigned FiniteModelMultiSorted::boolValue(bool isTrue)
{
  if (!env.signature->foolConstantsDefined()) {
    USER_ERROR("Cannot evaluate a boolean term: this model does not have a boolean domain");
  }
  DHMap<unsigned,unsigned> noSubst;
  return evaluateTerm(TermList(Term::createConstant(env.signature->getFoolConstantSymbol(isTrue))),noSubst);
}

unsigned FiniteModelMultiSorted::evaluateTerm(TermList tl, const DHMap<unsigned,unsigned>& subst)
{
  if (tl.isVar()) {
    // TODO: maybe error, if the variable is not in the map?

    // cout << "looking up for " << tl.var() << " returning " << subst.get(tl.var()) << endl;
    return subst.get(tl.var());
  }

  Term* term = tl.term();

  if (term->isSpecial()) {
    // A formula in term position; to a model that is just a boolean value, so evaluate it and
    // return the domain element the corresponding FOOL constant sits on. Both $true / $false at
    // term level and, say, p(a) for a p declared with an $o result sort (which the parser turns
    // into a predicate) arrive here. The remaining FOOL constructs we cannot evaluate.
    if (term->specialFunctor() != SpecialFunctor::FORMULA) {
      USER_ERROR("Cannot evaluate " + tl.toString() + ", not supported");
    }
    DHMap<unsigned,unsigned> inner(subst); // evaluateFormula wants to bind quantified variables
    return boolValue(evaluateFormula(term->getSpecialData()->getFormula(),inner));
  }

  unsigned f = term->functor();
  unsigned arity = env.signature->functionArity(f);
  DArray<unsigned> args(arity);
  for(unsigned i=0;i<arity;i++){
    args[i] = evaluateTerm(*term->nthArgument(i),subst);
    ASS_G(args[i],0)
  }

  // cout << "evaluateTerm " << tl.toString() << " under " << subst << endl;

  if (!funRepresented(f)) {
    // an eliminated symbol: evaluate through its symbolic definition
    Problem::FunDef* fd = symbolicFunDef(f);
    if (!fd->_body) {
      return 1; // "arbitrary value", fixed as the first domain element (as also printed by toString)
    }
    // a local substitution here, as the evaluation of the body may recurse into further symbolic definitions
    DHMap<unsigned,unsigned> inner;
    for(unsigned i=0;i<arity;i++){
      ASS(fd->_head->nthArgument(i)->isVar());
      inner.set(fd->_head->nthArgument(i)->var(),args[i]);
    }
    return evaluateTerm(TermList(fd->_body),inner);
  }

  const DArray<unsigned>& tbl = _f_tables[f];
  size_t idx = tableIndex(args,_sizes,env.signature->getFunction(f)->fnType());
  ASS_L(idx, tbl.size());

  if (tbl[idx] == 0) {
    // the model is represented, but does not say what f is on these arguments
    throw UndefinedValueException(env.signature->functionName(f));
  }
  return tbl[idx];
}

bool FiniteModelMultiSorted::evaluateLiteral(Literal* lit, const DHMap<unsigned,unsigned>& subst)
{
  unsigned p = lit->functor();
  unsigned arity = env.signature->predicateArity(p);
  DArray<unsigned> args(arity);
  for(unsigned i=0;i<arity;i++){
    args[i] = evaluateTerm(*lit->nthArgument(i),subst);
    ASS_G(args[i],0)
  }

  if(lit->isEquality()){
    return (args[0]==args[1]) == lit->polarity();
  }

  if (!predRepresented(p)) {
    // an eliminated symbol: evaluate through its symbolic definition
    Problem::PredDef* pd = symbolicPredDef(p);
    // a local substitution here, as the evaluation of the body may recurse into further symbolic definitions
    DHMap<unsigned,unsigned> inner;
    for(unsigned i=0;i<arity;i++){
      ASS(pd->_head->nthArgument(i)->isVar());
      inner.set(pd->_head->nthArgument(i)->var(),args[i]);
    }
    bool val = (evaluateFormula(pd->_body,inner) == pd->_head->isPositive());
    return val == lit->polarity();
  }

  const DArray<char>& tbl = _p_tables[p];
  size_t idx = tableIndex(args,_sizes,env.signature->getPredicate(p)->predType());

  ASS_L(idx, tbl.size());
  char res = tbl[idx];

  if(res==INTP_UNDEF) {
    // the model is represented, but does not say what p is on these arguments
    throw UndefinedValueException(env.signature->predicateName(p));
  }

  return (res==INTP_TRUE) == (lit->polarity());
}

void FiniteModelMultiSorted::eliminateSortFunctionsAndPredicates(const Stack<unsigned> &sortFunctions, const Stack<unsigned> &sortPredicates)
{
  // let's do functions first
  for(unsigned i = 0; i<sortFunctions.size(); i++) {
    unsigned elim_f = sortFunctions[i];
    Signature::Symbol* elim_symb = env.signature->getFunction(elim_f);
    ASS_EQ(elim_symb->arity(),1)
    unsigned srt = elim_symb->fnType()->result().term()->functor();

    DHSet<unsigned> f_range;
    DHMap<unsigned,unsigned> new_to_old;
    DHMap<unsigned,unsigned> old_to_new;

    unsigned origSize = _sizes[srt];
    unsigned newSize = 0;

    // srt's domain is getting reduced to the range of f
    {
      ASS(funRepresented(elim_f)); // Monotonicity bumps usageCnt of the sort functions it introduces
      const DArray<unsigned>& elim_tbl = _f_tables[elim_f];
      for(unsigned j = 1; j<=origSize; j++) {
        unsigned res = elim_tbl[j-1];
        //cout << "f(" << j << ")=" << res << endl;
        if (f_range.insert(res)) {
          newSize++;
          new_to_old.insert(newSize,res);
          old_to_new.insert(res,newSize);
        }
      }
    }

    // we will need to reencode everything

    // save the old stuff
    auto old_f_tables = std::move(_f_tables);
    auto old_p_tables = std::move(_p_tables);
    auto old_sizes = _sizes.clone();

    // update size of the affected sort
    _sizes[srt] = newSize;
    // cout << "newSize " << newSize << endl;
    initTables();

    // every function and predicate need to get reencoded
    // - arguments of sort srt now iterate over a different (likely smaller domain)
    // - function values of sort srt still need to passed through the ``disappearing'' elim_f

    for(unsigned f=0; f<env.signature->functions();f++){
      if (!funRepresented(f)) {
        ASS_EQ(old_f_tables[f].size(),0); // usageCnt did not change, so neither did representedness
        continue;
      }
      Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* sig = symb->fnType();
      unsigned arity = symb->arity();

      // cout << "f = " << f << " arity= " << arity << endl;

      DArray<unsigned>& tbl = _f_tables[f];
      const DArray<unsigned>& old_tbl = old_f_tables[f];

      DArray<unsigned> old_args(arity);
      size_t idx = 0; // ... will fly linearly through the new table
      ArgsEnumerator it(_sizes,sig,arity); // ... args will respect the (new) table encoding
      do {
        const DArray<unsigned>& args = it.args();
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        unsigned old_res = old_tbl[tableIndex(old_args,old_sizes,sig)];

        if (old_res) { // eliminated symbols don't have reasonable values
          unsigned res_srt = sig->result().term()->functor();
          unsigned res = (res_srt == srt) ?
                            // need to first pass old_res through elim_f, before mapping to the new domain
                            old_to_new.get(old_f_tables[elim_f][old_res-1]) :
                            old_res;

          tbl[idx] = res;
        }

        idx++;
      } while (it.next());
      ASS_EQ(idx,tbl.size());
    }

    for(unsigned p=1; p<env.signature->predicates();p++){
      if (!predRepresented(p)) {
        ASS_EQ(old_p_tables[p].size(),0); // usageCnt did not change, so neither did representedness
        continue;
      }
      Signature::Symbol* symb = env.signature->getPredicate(p);
      OperatorType* sig = symb->predType();
      unsigned arity = symb->arity();

      // cout << "p = " << p << " arity= " << arity << endl;

      DArray<char>& tbl = _p_tables[p];
      const DArray<char>& old_tbl = old_p_tables[p];

      DArray<unsigned> old_args(arity);
      size_t idx = 0; // ... will fly linearly through the new table
      ArgsEnumerator it(_sizes,sig,arity); // ... args will respect the (new) table encoding
      do {
        const DArray<unsigned>& args = it.args();
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        tbl[idx++] = old_tbl[tableIndex(old_args,old_sizes,sig)]; // no change for predicates
      } while (it.next());
      ASS_EQ(idx,tbl.size());
    }
  }

  // let's do predicates now
  for(unsigned i = 0; i<sortPredicates.size(); i++) {
    unsigned elim_p = sortPredicates[i];
    Signature::Symbol* elim_symb = env.signature->getPredicate(elim_p);
    ASS_EQ(elim_symb->arity(),1)
    unsigned srt = elim_symb->predType()->arg(0).term()->functor();

    // cout << "Eliminate p = " << elim_p << endl;

    DHMap<unsigned,unsigned> new_to_old;
    DHMap<unsigned,unsigned> old_to_new;

    unsigned origSize = _sizes[srt];
    unsigned newSize = 0;

    // srt's domain is getting reduced to those elements for which p is true
    {
      ASS(predRepresented(elim_p)); // the sort predicates occur in the added sort-predicate axioms
      const DArray<char>& elim_tbl = _p_tables[elim_p];
      for(unsigned j = 1; j<=origSize; j++) {
        char res = elim_tbl[j-1];
        // cout << "p(" << j << ")=" << (unsigned)res << endl;
        if (res == INTP_TRUE) {
          newSize++;
          new_to_old.insert(newSize,j);
          old_to_new.insert(j,newSize);
        }
      }
    }

    if (origSize == newSize)
      continue;

    // we will need to reencode everything

    // save the old stuff
    auto old_f_tables = std::move(_f_tables);
    auto old_p_tables = std::move(_p_tables);
    auto old_sizes = _sizes.clone();

    // update size of the affected sort
    _sizes[srt] = newSize;
    // cout << "origSize = " << origSize << " --> newSize = " << newSize << endl;

    initTables();

    // every function and predicate need to get reencoded
    // - arguments of sort srt now iterate over a different (likely smaller domain)

    for(unsigned f=0; f<env.signature->functions();f++){
      if (!funRepresented(f)) {
        ASS_EQ(old_f_tables[f].size(),0); // usageCnt did not change, so neither did representedness
        continue;
      }
      Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* sig = symb->fnType();
      unsigned arity = symb->arity();

      DArray<unsigned>& tbl = _f_tables[f];
      const DArray<unsigned>& old_tbl = old_f_tables[f];

      DArray<unsigned> old_args(arity);
      size_t idx = 0; // ... will fly linearly through the new table
      ArgsEnumerator it(_sizes,sig,arity); // ... args will respect the (new) table encoding
      do {
        const DArray<unsigned>& args = it.args();
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        unsigned old_res = old_tbl[tableIndex(old_args,old_sizes,sig)];

        if (old_res) { // eliminated symbols don't have reasonable values
          unsigned res_srt = sig->result().term()->functor();
          // this should be stipulated by the extra sort-predicate axioms
          ASS(res_srt != srt || old_p_tables[elim_p][old_res-1] == INTP_TRUE)

          unsigned res = (res_srt == srt) ? old_to_new.get(old_res) : old_res;
          tbl[idx] = res;
        }

        idx++;
      } while (it.next());
      ASS_EQ(idx,tbl.size());
    }

    for(unsigned p=1; p<env.signature->predicates();p++){
      if (!predRepresented(p)) {
        ASS_EQ(old_p_tables[p].size(),0); // usageCnt did not change, so neither did representedness
        continue;
      }
      Signature::Symbol* symb = env.signature->getPredicate(p);
      OperatorType* sig = symb->predType();
      unsigned arity = symb->arity();

      // cout << "p = " << p << " arity= " << arity << endl;

      DArray<char>& tbl = _p_tables[p];
      const DArray<char>& old_tbl = old_p_tables[p];

      DArray<unsigned> old_args(arity);
      size_t idx = 0; // ... will fly linearly through the new table
      ArgsEnumerator it(_sizes,sig,arity); // ... args will respect the (new) table encoding
      do {
        const DArray<unsigned>& args = it.args();
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        tbl[idx++] = old_tbl[tableIndex(old_args,old_sizes,sig)]; // no change for predicates
      } while (it.next());
      ASS_EQ(idx,tbl.size());
    }
  }
}

void FiniteModelMultiSorted::restoreEliminatedFunDef(Problem::FunDef* fd)
{
  unsigned f = fd->_head->functor();
  unsigned arity = env.signature->functionArity(f);

  DArray<unsigned> vars(arity);
  for(unsigned i=0;i<arity;i++){
    ASS(fd->_head->nthArgument(i)->isVar());
    vars[i] = fd->_head->nthArgument(i)->var();
  }

  static DHMap<unsigned,unsigned> subst;
  subst.reset();

  OperatorType* ot = env.signature->getFunction(f)->fnType();
  ArgsEnumerator it(_sizes,ot,arity);
  it.bindAll(vars,subst);
  do {
    unsigned val = evaluateTerm(TermList(fd->_body),subst);
    addFunctionDefinition(f,it.args(),val);
  } while (it.nextAndRebind(vars,subst));
}

void FiniteModelMultiSorted::materializeFun(unsigned f)
{
  ASS(!funRepresented(f));

  Problem::FunDef* fd = symbolicFunDef(f); // creates the trivial definition if there was no record

  // allocate the table ...
  Signature::Symbol* symb = env.signature->getFunction(f);
  DArray<unsigned> tbl;
  tbl.expand(tableSize(symb->fnType(),symb->arity(),_sizes),0);
  _f_tables[f] = std::move(tbl);

  // ... and fill it by evaluating the definition
  if (fd->_body) {
    restoreEliminatedFunDef(fd);
  } else { // "arbitrary value", fixed as the first domain element
    DArray<unsigned>& tbl = _f_tables[f];
    for(size_t idx = 0; idx < tbl.size(); idx++) {
      tbl[idx] = 1;
    }
  }

  _symbolicFuns.remove(f); // from now on, the explicit table speaks for f
}

void FiniteModelMultiSorted::restoreEliminatedPredDef(Problem::PredDef* pd)
{
  unsigned p = pd->_head->functor();
  unsigned arity = env.signature->predicateArity(p);

  DArray<unsigned> vars(arity);
  for(unsigned i=0;i<arity;i++){
    ASS(pd->_head->nthArgument(i)->isVar());
    vars[i] = pd->_head->nthArgument(i)->var();
  }

  static DHMap<unsigned,unsigned> subst;
  subst.reset();

  OperatorType* ot = env.signature->getPredicate(p)->fnType();
  ArgsEnumerator it(_sizes,ot,arity);
  it.bindAll(vars,subst);
  do {
    bool val = (evaluateFormula(pd->_body,subst) == pd->_head->isPositive());
    addPredicateDefinition(p,it.args(),val);
  } while (it.nextAndRebind(vars,subst));
}

void FiniteModelMultiSorted::materializePred(unsigned p)
{
  ASS(!predRepresented(p));

  Problem::PredDef* pd = symbolicPredDef(p); // creates the trivial definition if there was no record

  // allocate the table ...
  Signature::Symbol* symb = env.signature->getPredicate(p);
  DArray<char> tbl;
  tbl.expand(tableSize(symb->predType(),symb->arity(),_sizes),0);
  _p_tables[p] = std::move(tbl);

  // ... and fill it by evaluating the definition
  restoreEliminatedPredDef(pd);

  _symbolicPreds.remove(p); // from now on, the explicit table speaks for p
}

// does p occur anywhere in f? SubformulaIterator descends into the arguments of a literal
// too, so a predicate hiding inside a formula in term position is found as well
static bool mentionsPredicate(Formula* f, unsigned p)
{
  SubformulaIterator sfit(f);
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    if (sf->connective() == LITERAL && sf->literal()->functor() == p) {
      return true;
    }
  }
  return false;
}

bool FiniteModelMultiSorted::prepareForFlip(unsigned p)
{
  // there has to be a table to flip into
  if (!predRepresented(p)) {
    if (!_symbolicPreds.find(p)) {
      // we have not committed to any interpretation of p yet, so flipping it is a no-op --
      // and the definition still to be recorded (this happens for the GLOB_FLIPs, which are
      // replayed before any definition) will simply take over. Materializing here would be
      // actively wrong: symbolicPredDef would invent a trivial "p <=> $false" record, which
      // the real definition, arriving later, would then find the key already taken by.
      return false;
    }
    materializePred(p);
  }

  // A flip's soundness argument reads: the model that differs from this one *only on p*, as
  // prescribed, is a model of the problem as it was before the flip's own preprocessing step.
  // A symbolic definition whose body reads p breaks that "only": it silently moves along as
  // soon as p's table is written -- during the flip's own loop, when it can also reach the
  // condition being tested, and after it. So freeze such definitions here; materializing does
  // not change what the model says, it only stops it from shifting under the flip.
  // Direct readers are enough: once a reader is explicit, a definition that reads *it* no
  // longer moves either. _symbolicFuns need no treatment -- their bodies are terms, produced
  // by function definition elimination, so they cannot mention a predicate at all.
  Stack<unsigned> readers;
  DHMap<unsigned,Problem::PredDef*>::Iterator it(_symbolicPreds);
  while (it.hasNext()) {
    unsigned q;
    Problem::PredDef* pd;
    it.next(q,pd);
    if (mentionsPredicate(pd->_body,p)) {
      readers.push(q);
    }
  }
  // collected first, as materializePred both removes from _symbolicPreds and,
  // through symbolicPredDef, may insert into it
  for (unsigned q : readers) {
    materializePred(q);
  }
  return true;
}

void FiniteModelMultiSorted::restoreGlobalPredicateFlip(Problem::GlobalFlip* gf)
{
  // a full-table pass with a value independent of the arguments -- a linear scan suffices
  DArray<char>& tbl = _p_tables[gf->_pred];
  for(size_t idx = 0; idx < tbl.size(); idx++) {
    if (tbl[idx] == INTP_TRUE) {
      tbl[idx] = INTP_FALSE;
    } else { // includes INTP_UNDEF, which is implicitly false
      tbl[idx] = INTP_TRUE;
    }
  }
}

void FiniteModelMultiSorted::restoreViaCondFlip(Problem::CondFlip* cf)
{
  // cf->outputDefinition(cout);

  DHMap<unsigned,TermList> sortMap;
  SortHelper::collectVariableSorts(cf->_val,sortMap);
  SortHelper::collectVariableSorts(cf->_cond,sortMap); // in bce, cond can have extra variables; we could treat them existentially, but this may be wrong for _fixedPoint-ers
  unsigned arity = sortMap.size();

  // cout << "arity: " << arity << " " << sortMap << endl;

  /*
  // we need to existentially close cond for all variables except those of _val
  VList* freeVars = freeVariables(cf->_cond);

  // cout << "freeVars: " << *freeVars << endl;

  {
    // now filter freeVars and drop all mentioned by _val
    VList** l = &freeVars;
    while (*l) {
      unsigned var = (*l)->head();
      if (sortMap.findPtr(var)) { // drop this one
        VList* dead = *l;
        *l = (*l)->tail(); // keep l where it is, but reconnect *l
        delete dead;
      } else { // simply move on with l
        l = (*l)->tailPtr();
      }
    }
  }
  // cout << "filtered: " << *freeVars << endl;

  Formula* closedCond = freeVars ? new QuantifiedFormula(EXISTS,freeVars,0,cf->_cond) : cf->_cond;

  // cout << "closedCond: " << closedCond->toString() << endl;
  */

  static DArray<unsigned> vars;
  vars.ensure(arity);
  static DArray<unsigned> sorts;
  sorts.ensure(arity);

  unsigned i = 0;
  DHMap<unsigned,TermList>::Iterator it(sortMap); // non-deterministic order OK?
  while (it.hasNext()) {
    unsigned var;
    TermList srt;
    it.next(var,srt);
    vars[i] = var;
    sorts[i] = srt.term()->functor();
    i++;
  }

  bool flipped;
  do {
    flipped = false;

    static DHMap<unsigned,unsigned> subst;

    unsigned p = cf->_val->functor();
    ASS_NEQ(p,0) // equality cannot be flipped!
    unsigned p_arity = env.signature->predicateArity(p);
    static DArray<unsigned> inner_args;
    inner_args.ensure(p_arity);

    DArray<unsigned> bounds(arity);
    for(unsigned i=0;i<arity;i++){ bounds[i] = _sizes[sorts[i]]; }
    ArgsEnumerator it(std::move(bounds));
    it.bindAll(vars,subst);
    do {
      if (evaluateFormula(cf->_cond,subst) != cf->_neg) {
        // do the flip
        for(unsigned j=0;j<p_arity;j++){
          inner_args[j] = evaluateTerm(*cf->_val->nthArgument(j),subst);
        }
        DArray<char>& tbl = _p_tables[p];
        size_t idx = tableIndex(inner_args,_sizes,env.signature->getPredicate(p)->predType());
        ASS_L(idx, tbl.size());

        char before = tbl[idx];
        char after = (cf->_val->isPositive() ? INTP_TRUE : INTP_FALSE);
        tbl[idx] = after;
        flipped |= (before != after);
      }
    } while (it.nextAndRebind(vars,subst));
  } while (cf->_fixedPoint && flipped);
  // cout << endl;
}

/**
 * Replay the recorded interferences in reverse (LIFO) order, turning the model of the
 * fully preprocessed problem into a model of the original one.
 *
 * FUN_DEFs and PRED_DEFs are merely *recorded* (into _symbolicFuns/_symbolicPreds) rather
 * than expanded into explicit tables; evaluation and printing consult the records lazily.
 * A definition recorded now may reference a predicate q that a flip replayed later still
 * modifies -- lazy evaluation then reroutes through the post-flip q. Where that is sound:
 *  - FunDef bodies are terms, so they cannot mention predicates, and function tables are
 *    never modified after the recording point -- immune;
 *  - a genuine definition (PredicateDefinition/FunctionDefinition elimination) is a unit of
 *    the original problem, which pins the defined symbol uniquely given the other symbols;
 *    the lazy reading satisfies it by construction at every replay stage.
 *
 * Where it is not sound is a flip: its argument reads "the model that differs from this one
 * *only on q* is a model of the problem as it was before this step", and a lazy definition
 * reading q silently moves along, so that hypothesis fails. It fails inside the flip's own
 * loop too -- restoreViaCondFlip re-evaluates the condition per grounding, and the condition
 * can reach q through such a definition, making it chase a moving target. So prepareForFlip
 * makes q, and every recorded definition reading q, explicit first; see there.
 *
 * The GLOB_FLIPs are the one kind that needs none of this in practice: polarity flipping runs
 * as the very last preprocessing step, so they are replayed before any definition is recorded,
 * and prepareForFlip finds nothing to freeze -- indeed nothing to flip either, for a target
 * the model does not represent yet. They go through the same path all the same, so that the
 * replay does not silently depend on that ordering.
 */
void FiniteModelMultiSorted::restoreEliminatedDefinitions(Kernel::Problem* prob)
{
  auto ii = prob->interferences.iter(); // LIFO is the key here!
  while (ii.hasNext()) {
    Problem::Interference* i = ii.next();
    switch (i->_kind) {
      case Problem::IntereferenceKind::FUN_DEF: {
        Problem::FunDef* fd = static_cast<Problem::FunDef*>(i);
        _symbolicFuns.insert(fd->_head->functor(),fd);
        break;
      }
      case Problem::IntereferenceKind::PRED_DEF: {
        Problem::PredDef* pd = static_cast<Problem::PredDef*>(i);
        _symbolicPreds.insert(pd->_head->functor(),pd);
        break;
      }
      case Problem::IntereferenceKind::GLOB_FLIP: {
        Problem::GlobalFlip* gf = static_cast<Problem::GlobalFlip*>(i);
        if (prepareForFlip(gf->_pred)) {
          restoreGlobalPredicateFlip(gf);
        }
        break;
      }
      case Problem::IntereferenceKind::COND_FLIP: {
        Problem::CondFlip* cf = static_cast<Problem::CondFlip*>(i);
        if (prepareForFlip(cf->_val->functor())) {
          restoreViaCondFlip(cf);
        }
        break;
      }

      default:
        ASSERTION_VIOLATION
    }
  }

  // A table cell still undefined at this point was never asked about during the replay
  // (a read would have thrown); make the default explicit, so that printing -- which goes
  // to the cells directly -- and any later evaluation see a total model.
  for(unsigned f=0; f<env.signature->functions();f++){
    DArray<unsigned>& tbl = _f_tables[f];
    for(size_t idx = 0; idx < tbl.size(); idx++) {
      if (tbl[idx] == 0)
        tbl[idx] = 1;
    }
  }
  for(unsigned p=1; p<env.signature->predicates();p++){
    DArray<char>& tbl = _p_tables[p];
    for(size_t idx = 0; idx < tbl.size(); idx++) {
      if (tbl[idx] == INTP_UNDEF)
        tbl[idx] = INTP_FALSE;
    }
  }
}

/**
 * Evaluate a unit in this model; throws UndefinedValueException as soon as the model
 * turns out not to say what some symbol is on the arguments at hand.
 */
bool FiniteModelMultiSorted::evaluate(Unit* unit)
{
  Formula* formula = (unit->isClause()) ?
    Formula::fromClause(unit->asClause()) : // universally closed by default
    Formula::quantify(static_cast<FormulaUnit*>(unit)->getFormula()); // close over any free variables (a no-op on closed formulas)

  DHMap<unsigned,unsigned> subst;
  return evaluateFormula(formula,subst);
}

/**
 *
 * TODO: This is recursive, which could be problematic in the long run
 *
 */
bool FiniteModelMultiSorted::evaluateFormula(Formula* formula, DHMap<unsigned,unsigned>& subst)
{
  bool isAnd = false;
  bool isImp = false;
  bool isXor = false;
  bool isForall = false;
  switch(formula->connective()){
    case FALSE:
      return false;
    case TRUE:
      return true;

    case LITERAL:
      return evaluateLiteral(formula->literal(),subst);

    // the dual of the FORMULA special term in evaluateTerm: a boolean term used as a formula
    case BOOL_TERM:
      return evaluateTerm(formula->getBooleanTerm(),subst) == boolValue(true);

    case NOT:
      return !evaluateFormula(formula->uarg(),subst);
    case AND:
      isAnd=true;
    case OR:
      {
        FormulaList* args = formula->args();
        FormulaList::Iterator fit(args);
        while(fit.hasNext()){
          Formula* arg = fit.next();
          bool res = evaluateFormula(arg,subst);
          if(isAnd && !res) return false;
          if(!isAnd && res) return true;
        }
        return isAnd;
      }

    case IMP:
      isImp=true;
    case XOR:
      isXor = !isImp;
    case IFF:
    {
      Formula* left = formula->left();
      Formula* right = formula->right();
      bool left_res = evaluateFormula(left,subst);
      if(isImp && !left_res) return true;
      bool right_res = evaluateFormula(right,subst);
      if(isImp) return right_res;

#if DEBUG_MODEL
      cout << "left_res is " << left_res << ", right_res is " << right_res << endl;
#endif

      if(isXor) return left_res != right_res;
      return left_res == right_res; // IFF
    }

    // Expand quantifications
    case FORALL:
      isForall = true;
    case EXISTS:
    {
      VSList* vs = formula->vars();

      // cout << "will do FORALL/EXISTS for " << formula->toString() << endl;

      unsigned arity = VSList::length(vs);
      DArray<unsigned> old_vals(arity);
      DArray<unsigned> vars(arity);
      DArray<unsigned> bounds(arity);

      // store old_vals, figure out bounds
      for(unsigned i=0;i<arity;i++){
        auto [var, srt] = vs->head();
        vs = vs->tail();
        vars[i] = var;
        bounds[i] = _sizes[srt.term()->functor()];
        old_vals[i] = subst.get(var,0);
      }

      ArgsEnumerator it(std::move(bounds));
      it.bindAll(vars,subst);

      bool res;
      bool early = false;
      do {
        res = evaluateFormula(formula->qarg(),subst);

        if((isForall && !res) || (!isForall && res)) {
          early = true;
          break;
        }
      } while (it.nextAndRebind(vars,subst));

      // undo the bindings in subst
      for(unsigned i=0;i<arity;i++){
        subst.set(vars[i],old_vals[i]);
      }

      if (early) {
        if(isForall && !res) return false;
        if(!isForall && res) return true;
      }

      return isForall;
    }
    default:
      USER_ERROR("Cannot evaluate " + formula->toString() + ", not supported");
  }
}

}
