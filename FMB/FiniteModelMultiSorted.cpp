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

// computes the number of rows of the table of a symbol of type sig under the domain sizes sizes
// (a 0-sized dimension -- an unused interpreted sort -- counts as 1, matching tableIndex, where such a dimension contributes no stride)
static size_t tableSize(OperatorType* sig, unsigned arity, const DArray<unsigned>& sizes)
{
  size_t size = 1;
  for(unsigned i=0;i<arity;i++) {
    unsigned mult = sizes[sig->arg(i).term()->functor()];
    if (mult > 1 && size > SIZE_MAX / mult) {
      INVALID_OPERATION("Model too large to represent!");
    }
    size *= (mult>0 ? mult : 1);
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

void FiniteModelMultiSorted::addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res)
{
  ASS_EQ(env.signature->functionArity(f),args.size());

  DArray<unsigned>& tbl = _f_tables[f];
  size_t idx = tableIndex(args,_sizes,env.signature->getFunction(f)->fnType());

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
    if(env.signature->isInterpretedNonDefault(s))
      continue;

    std::string sortName = env.signature->typeConName(s);
    std::string sortNameLabel = (env.signature->isBoolCon(s)) ? "bool" : sortName;

    // skip declaring $i, we know what it is
    if(!env.signature->isDefaultSortCon(s))
      // Sort declaration
      modelStm << "tff(" << prepend("declare_", sortNameLabel) << ",type,"<<sortName<<":$tType)." <<endl;

    cnames[s].ensure(size+1);

    // Domain constant declarations
    for(unsigned i=1;i<=size;i++){
      modelStm << "tff(" << append(prepend("declare_", sortNameLabel), Int::toString(i).c_str()) << ",type,";
      std::string cname = append(prepend("fmb_", sortNameLabel),(std::string("_")+Lib::Int::toString(i)).c_str());
      cnames[s][i]=cname;
      modelStm << cname << ":" << sortName << ")." << endl;
    }

    //Output domain
    modelStm << "tff(" << prepend("finite_domain_", sortNameLabel) << ",axiom," << endl;
    modelStm << "      ! [X:" << sortName << "] : (" << endl;
    modelStm << "         ";
    for(unsigned i=1;i<=size;i++){
      modelStm << "X = " << cnames[s][i];
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
      Problem::FunDef* fd;
      if (!_symbolicFuns.find(f,fd)) { // implicitly eliminated symbol, let's define trivially
        // need a linear head and empty body as a place-holder for fmb_$sort_1

        // create linear term f(X0,X1,...X_arity)
        TermStack args;
        for (unsigned v = 0; v < arity; v++) {
          args.push(TermList::var(v));
        }
        fd = new Problem::FunDef(Term::create(f,args.size(),args.begin()),nullptr /* arbitrary value */);
        _symbolicFuns.insert(f,fd);
      }

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
      Problem::PredDef* pd;
      if (!_symbolicPreds.find(p,pd)) { // implicitly eliminated symbol, let's define as $false
        // need a linear head and $false for a body
        TermStack args;
        for (unsigned v = 0; v < env.signature->getPredicate(p)->arity(); v++) {
          args.push(TermList::var(v));
        }
        pd = new Problem::PredDef(Literal::create(p, args.size(), true, args.begin()),new Formula(false));
        _symbolicPreds.insert(p,pd);
      }

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

unsigned FiniteModelMultiSorted::evaluateTerm(TermList tl, const DHMap<unsigned,unsigned>& subst)
{
  if (tl.isVar()) {
    // TODO: maybe error, if the variable is not in the map?

    // cout << "looking up for " << tl.var() << " returning " << subst.get(tl.var()) << endl;
    return subst.get(tl.var());
  }

  Term* term = tl.term();
  unsigned f = term->functor();
  unsigned arity = env.signature->functionArity(f);
  DArray<unsigned> args(arity);
  for(unsigned i=0;i<arity;i++){
    args[i] = evaluateTerm(*term->nthArgument(i),subst);
    ASS_G(args[i],0)
  }

  // cout << "evaluateTerm " << tl.toString() << " under " << subst << endl;

  const DArray<unsigned>& tbl = _f_tables[f];
  size_t idx = tableIndex(args,_sizes,env.signature->getFunction(f)->fnType());
  ASS_L(idx, tbl.size());

  if (tbl[idx] == 0) {
    _implicitlyEliminatedFunctions.insert(f);
    return 1;
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

  const DArray<char>& tbl = _p_tables[p];
  size_t idx = tableIndex(args,_sizes,env.signature->getPredicate(p)->predType());

  ASS_L(idx, tbl.size());
  char res = tbl[idx];

  if(res==INTP_UNDEF) {
    _implicitlyEliminatedPredicates.insert(p);
    return !lit->polarity();
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

void FiniteModelMultiSorted::restoreImplicitlyEliminatedFun(unsigned f)
{
  // a full-table pass with a value independent of the arguments -- a linear scan suffices
  DArray<unsigned>& tbl = _f_tables[f];
  for(size_t idx = 0; idx < tbl.size(); idx++) {
    tbl[idx] = 1;
  }
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

void FiniteModelMultiSorted::restoreImplicitlyEliminatedPred(unsigned p)
{
  // a full-table pass with a value independent of the arguments -- a linear scan suffices
  DArray<char>& tbl = _p_tables[p];
  for(size_t idx = 0; idx < tbl.size(); idx++) {
    if (tbl[idx] == INTP_UNDEF) // default only conditionally (some flips may have already been done)
      tbl[idx] = INTP_FALSE;
  }
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
      case Problem::IntereferenceKind::GLOB_FLIP:
        restoreGlobalPredicateFlip(static_cast<Problem::GlobalFlip*>(i));
        break;
      case Problem::IntereferenceKind::COND_FLIP:
        restoreViaCondFlip(static_cast<Problem::CondFlip*>(i));
        break;

      default:
        ASSERTION_VIOLATION
    }

    // we try to give the implicitlyEliminated proper meaning as soon as possible, so that COND_FLIP's could go and flip the restored defs

    auto iief = _implicitlyEliminatedFunctions.iter();
    while (iief.hasNext()) {
      restoreImplicitlyEliminatedFun(iief.next());
    }
    _implicitlyEliminatedFunctions.reset();
    auto iiep = _implicitlyEliminatedPredicates.iter();
    while (iiep.hasNext()) {
      restoreImplicitlyEliminatedPred(iiep.next());
    }
    _implicitlyEliminatedPredicates.reset();
  }
}

bool FiniteModelMultiSorted::evaluate(Unit* unit)
{
  Formula* formula = (unit->isClause()) ?
    Formula::fromClause(unit->asClause()) :
    static_cast<FormulaUnit*>(unit)->getFormula();

  DHMap<unsigned,unsigned> subst;
  bool res = evaluateFormula(formula,subst);
  if (_implicitlyEliminatedFunctions.size() > 0 || _implicitlyEliminatedPredicates.size() > 0) {
    USER_ERROR("Encountered an undefined symbol while evaluating a Unit");
  }
  return res;
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
