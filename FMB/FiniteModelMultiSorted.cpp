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

#include "FiniteModelMultiSorted.hpp"

#define DEBUG_MODEL 0

namespace FMB{

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

void FiniteModelMultiSorted::initTables()
{
  _f_offsets.ensure(env.signature->functions());
  _p_offsets.ensure(env.signature->predicates());

  // generate offsets per function for indexing f_interpreation
  // see addFunctionDefinition for how the offset is used to compute
  // the actual index
  unsigned offsets=0;
  for(unsigned f=0; f<env.signature->functions();f++){
    unsigned arity=env.signature->functionArity(f);
    _f_offsets[f]=offsets;

    OperatorType* sig = env.signature->getFunction(f)->fnType();
    unsigned add = 1;
    for(unsigned i=0;i<arity;i++) {
      add *= _sizes[sig->arg(i).term()->functor()];
    }

    if (UINT_MAX - add <= offsets) {
      // the SAT solver skipped some functions as they are eliminated
      // (the model, on the other hand, should be prepared to hold their values later too)
      INVALID_OPERATION("Model too large to represent!");
    }

    offsets += add;
  }
  _f_interpretation.expand(offsets,0);
  // can restart for predicates as indexing p_interepration instead
  offsets=0;
  for(unsigned p=1; p<env.signature->predicates();p++){
    unsigned arity=env.signature->predicateArity(p);
    _p_offsets[p]=offsets;

    OperatorType* sig = env.signature->getPredicate(p)->predType();
    unsigned add = 1;
    for(unsigned i=0;i<arity;i++) {
      int mult = _sizes[sig->arg(i).term()->functor()];
      ASS(mult>0);
      add *= (mult>0 ? mult : 1);
    }

    if (UINT_MAX - add <= offsets) {
      // the SAT solver skipped some functions as they are eliminated
      // (the model, on the other hand, should be prepared to hold their values later too)
      INVALID_OPERATION("Model too large to represent!");
    }

    offsets += add;
  }
  _p_interpretation.expand(offsets,0);

  sortRepr.ensure(env.signature->typeCons());
  for(unsigned s=0;s<env.signature->typeCons();s++){
    if(env.signature->isInterpretedNonDefault(s))
      continue;
    sortRepr[s].ensure(_sizes[s]+1);
    for(unsigned i=0;i<=_sizes[s];i++){
      sortRepr[s][i] = -1;
    }
  }
}

void FiniteModelMultiSorted::addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res)
{
  ASS_EQ(env.signature->functionArity(f),args.size());

  unsigned arity = args.size();

  // this is just for collecting names for domain elements (not used unless replace_domain_elements==true)
  if(arity==0 && !env.signature->getFunction(f)->introduced()){
    TermList srt = env.signature->getFunction(f)->fnType()->result();
    unsigned srtU = srt.term()->functor();
    if(sortRepr[srtU][res] == -1){
      //cout << "Rep " << env.signature->functionName(f) << " for ";
      //cout << env.sorts->sortName(srt) << " and " << res << endl;
      sortRepr[srtU][res]=f;
    }
  }

  unsigned var = args2var(args,_sizes,_f_offsets,f,env.signature->getFunction(f)->fnType());

  ASS_L(var, _f_interpretation.size());
  _f_interpretation[var] = res;
}

void FiniteModelMultiSorted::addPredicateDefinition(unsigned p, const DArray<unsigned>& args, bool res)
{
  ASS_EQ(env.signature->predicateArity(p),args.size());

  //cout << "addPredicateDefinition for " << p << "(" << env.signature->predicateName(p) << ")" << endl;

  unsigned var = args2var(args,_sizes,_p_offsets,p,env.signature->getPredicate(p)->predType());

  ASS_L(var, _p_interpretation.size());
  _p_interpretation[var] = (res ? INTP_TRUE : INTP_FALSE);
}

std::string FiniteModelMultiSorted::toString()
{
  std::ostringstream modelStm;

  bool printIntroduced = false;

  bool replaceDomainConstants = env.options->replaceDomainElements();

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
      int frep = replaceDomainConstants ? sortRepr[s][i] : -1;
      std::string cname = (frep >= 0) ? env.signature->functionName(frep) : append(prepend("fmb_", sortNameLabel),(std::string("_")+Lib::Int::toString(i)).c_str());
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

  //Constants
  for(unsigned f=0;f<env.signature->functions();f++){
    Signature::Symbol* symb = env.signature->getFunction(f);
    // if(symb->usageCnt()==0) continue;
    unsigned arity = symb->arity();
    if(arity>0) continue;
    if(!printIntroduced && symb->introduced()) continue;
    std::string name = symb->name();
    unsigned res = _f_interpretation[_f_offsets[f]];

    if (res == 0) res = 1; // undefined defaults to the least available element

    TermList srtT = symb->fnType()->result();
    unsigned srt = srtT.term()->functor();
    std::string cname = cnames[srt][res];
    if(name == cname) continue;

    std::string sortName = env.signature->typeConName(srt);
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<":"<<sortName<<")."<<endl;
    // if(res>0){
      modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<<" = " << cname << ")."<<endl;
    /*}
    else{
      modelStm << "% " << name << " undefined in model" << endl;
    }*/
  }

  //Functions
  for(unsigned f=0;f<env.signature->functions();f++){
    Signature::Symbol* symb = env.signature->getFunction(f);
    // if(symb->usageCnt()==0) continue;
    unsigned arity = symb->arity();
    if(arity==0) continue;
    if(!printIntroduced && symb->introduced()) continue;
    std::string name = symb->name();
    OperatorType* sig = symb->fnType();
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<": (";
    for(unsigned i=0;i<arity;i++){
      modelStm << sig->arg(i).toString();
      if(i+1 < arity) modelStm << " * ";
    }
    modelStm << ") > " << sig->result().toString() << ")." << endl;

    modelStm << "tff("<<prepend("function_", name)<<",axiom,"<<endl;

    unsigned offset = _f_offsets[f];

    static DArray<unsigned> args;
    args.ensure(arity);
    for(unsigned i=0;i<arity;i++) args[i]=1;
    args[arity-1]=0;
    bool first=true;
fModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        TermList argST = sig->arg(i);
        unsigned argS = argST.term()->functor();
        if(args[i]==_sizes[argS]){
          args[i]=1;
        }
        else{
          args[i]++;

          //TODO could probably compute this directly, instead of via args
          // my mind isn't in the right place to do that now though!
          unsigned var = offset;
          unsigned mult=1;
          for(unsigned i=0;i<args.size();i++){
            var += mult*(args[i]-1);
            unsigned s = sig->arg(i).term()->functor();
            mult *= _sizes[s];
          }
          unsigned res = _f_interpretation[var];

          if (res == 0) res = 1; // undefined defaults to the least available element

          // if(res>0){
          if(!first){ modelStm << "         & " ; }
          else{ modelStm << "           " ; }
          first=false;
          /* }
          else{
            modelStm << "%         ";
          } */
          modelStm << name << "(";
          for(unsigned j=0;j<arity;j++){
            if(j!=0) modelStm << ",";
            TermList argSortT = sig->arg(j);
            unsigned argSort = argSortT.term()->functor();
            modelStm << cnames[argSort][args[j]];
          }
          // if(res>0){
          TermList resultSortT = sig->result();
          unsigned resultSort = resultSortT.term()->functor();
          modelStm << ") = " << cnames[resultSort][res] << endl;
          /* }
          else{
            modelStm << ") undefined in model" << endl;
          }
          */
          goto fModelLabel;
        }
      }
      modelStm << endl << ")." << endl << endl;
  }

  //Propositions
  for(unsigned p=1;p<env.signature->predicates();p++){
    unsigned arity = env.signature->predicateArity(p);
    if(arity>0) continue;
    Signature::Symbol* symb = env.signature->getPredicate(p);
    if(!printIntroduced && symb->introduced()) continue;
    // if(symb->usageCnt() == 0) continue;
    std::string name = symb->name();
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<": $o)."<<endl;
    char res = _p_interpretation[_p_offsets[p]];
    if(res==INTP_TRUE){
      modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<< ")."<<endl;
    } else { // covers (res==INTP_FALSE) as well as undefined, which defaults to false
      modelStm << "tff("<<append(name,"_definition")<<",axiom,~"<<name<< ")."<<endl;
    }
  }

  //Predicates
  for(unsigned p=1;p<env.signature->predicates();p++){
    Signature::Symbol* symb = env.signature->getPredicate(p);
    unsigned arity = symb->arity();
    if(arity==0) continue;
    if(!printIntroduced && symb->introduced()) continue;
    // if(symb->usageCnt() == 0) continue;
    std::string name = symb->name();
    OperatorType* sig = symb->predType();
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<": (";
    for(unsigned i=0;i<arity;i++){
      TermList argST = sig->arg(i);
      unsigned argS = argST.term()->functor();
      modelStm << env.signature->typeConName(argS);
      if(i+1 < arity) modelStm << " * ";
    }
    modelStm << ") > $o)." << endl;

    modelStm << "tff("<<prepend("predicate_", name)<<",axiom,"<<endl;

    unsigned offset = _p_offsets[p];

    static DArray<unsigned> args;
    args.ensure(arity);
    for(unsigned i=0;i<arity;i++) args[i]=1;
    args[arity-1]=0;
    bool first=true;
pModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){
        TermList argST = sig->arg(i);
        unsigned argS = argST.term()->functor();
        if(args[i]==_sizes[argS]){
          args[i]=1;
        }
        else{
          args[i]++;

          //TODO could probably compute this directly, instead of via args
          // my mind isn't in the right place to do that now though!
          unsigned var = offset;
          unsigned mult=1;
          for(unsigned i=0;i<args.size();i++){
            var += mult*(args[i]-1);
            unsigned s = sig->arg(i).term()->functor();
            mult *= _sizes[s];
          }
          char res = _p_interpretation[var];

          if (res == INTP_UNDEF) res = INTP_FALSE; // undefined defaults to false

          // if(res>INTP_UNDEF){
            if(!first){ modelStm << "         & " ; }
            else{ modelStm << "           " ; }
            first=false;
          /* }
          else{
            modelStm << "%         ";
          }
          */
          if(res==INTP_FALSE) modelStm << "~";
          modelStm << name << "(";
          for(unsigned j=0;j<arity;j++){
            if(j!=0) modelStm << ",";
            TermList argSortT = sig->arg(j);
            unsigned argSort = argSortT.term()->functor();
            modelStm << cnames[argSort][args[j]];
          }
          modelStm << ")";
          /*
          if(res==INTP_UNDEF){
            modelStm << " undefined in model";
          }
          */
          modelStm << endl;
          goto pModelLabel;
        }
      }
      modelStm << endl << ")." << endl << endl;
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

  unsigned var = args2var(args,_sizes,_f_offsets,f,env.signature->getFunction(f)->fnType());
  ASS_L(var, _f_interpretation.size());

  // cout << "var " << var << " _f_interpretation[var] " << _f_interpretation[var] << endl;
  if (_f_interpretation[var] == 0) {
    _implicitlyEliminatedFunctions.insert(f);
    return 1;
  }
  return _f_interpretation[var];
}

unsigned FiniteModelMultiSorted::evaluateGroundTerm(Term* term)
{
  ASS(term->ground());

#if DEBUG_MODEL
  cout << "evaluating ground term " << term->toString() << endl;
  cout << "domain constant status " << isDomainConstant(term) << endl;
#endif
  if(isDomainConstant(term)) return getDomainConstant(term).first;

  unsigned arity = env.signature->functionArity(term->functor());
  DArray<unsigned> args(arity);
  for(unsigned i=0;i<arity;i++){
    args[i] = evaluateGroundTerm(term->nthArgument(i)->term());
    if(args[i]==0) USER_ERROR("Could not evaluate "+term->toString());
  }

  OperatorType* sig = env.signature->getFunction(term->functor())->fnType();
  unsigned var = _f_offsets[term->functor()];
  unsigned mult = 1;
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    unsigned s = sig->arg(i).term()->functor();
    mult *=_sizes[s];
  }
#if VDEBUG
  if((term->functor()+1)<_f_offsets.size()) ASS_L(var,_f_offsets[term->functor()+1]);
#endif
  ASS_L(var,_f_interpretation.size());

  return _f_interpretation[var];
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

  unsigned var = args2var(args,_sizes,_p_offsets,p,env.signature->getPredicate(p)->predType());

  ASS_L(var, _p_interpretation.size());
  char res = _p_interpretation[var];

  if(res==INTP_UNDEF) {
    _implicitlyEliminatedPredicates.insert(p);
    return !lit->polarity();
  }

  return (res==INTP_TRUE) == (lit->polarity());
}

bool FiniteModelMultiSorted::evaluateGroundLiteral(Literal* lit)
{
  ASS(lit->ground());

#if DEBUG_MODEL
  cout << "Evaluating ground literal " << lit->toString() << endl;
#endif

  // evaluate all arguments
  unsigned arity = env.signature->predicateArity(lit->functor());
  DArray<unsigned> args(arity);
  for(unsigned i=0;i<arity;i++){
    args[i] = evaluateGroundTerm(lit->nthArgument(i)->term());
    if(args[i]==0) USER_ERROR("Could not evaluate "+lit->toString()+
                    " on "+(lit->nthArgument(i)->term()->toString())+
                    ", probably a partial model");
  }

  if(lit->isEquality()){
    bool res = args[0]==args[1];
#if DEBUG_MODEL
    cout << "Evaluate equality, args " << args[0] << " and " << args[1] << endl;
    cout << "res is " << (lit->polarity() ? res : !res) << endl;
#endif
    if(lit->polarity()) return res;
    else return !res;
  }

  OperatorType* sig = env.signature->getPredicate(lit->functor())->predType();
  unsigned var = _p_offsets[lit->functor()];
  unsigned mult = 1;
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    unsigned s = sig->arg(i).term()->functor();
    mult *=_sizes[s];
  }

#if VDEBUG
  if((lit->functor()+1)<_p_offsets.size()) ASS_L(var,_p_offsets[lit->functor()+1]);
#endif
  ASS_L(var,_p_interpretation.size());

  char res = _p_interpretation[var];
#if DEBUG_MODEL
    cout << "res is " << res << " and polarity is " << lit->polarity() << endl;
#endif

  if(res==INTP_UNDEF)
    USER_ERROR("Could not evaluate "+lit->toString()+", probably a partial model");

  return (res==INTP_TRUE) == (lit->polarity());
}

void FiniteModelMultiSorted::eliminateSortFunctionsAndPredicates(const Stack<unsigned> &sortFunctions, const Stack<unsigned> &sortPredicates)
{
  // if we already started evaluating things with the model, elimination would be more complicated
  ASS_EQ(_domainConstants.size(),0);
  ASS_EQ(_domainConstantsRev.size(),0);

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
      unsigned var = _f_offsets[elim_f];
      for(unsigned j = 1; j<=origSize; j++) {
        unsigned res = _f_interpretation[var++];
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
    auto old_f_offsets        = std::move(_f_offsets);
    auto old_f_interpretation = std::move(_f_interpretation);
    auto old_p_offsets        = std::move(_p_offsets);
    auto old_p_interpretation = std::move(_p_interpretation);
    auto old_sizes = _sizes.clone();

    // update size of the affected sort
    _sizes[srt] = newSize;
    // cout << "newSize " << newSize << endl;
    initTables();

    // every function and predicate need to get reencoded
    // - arguments of sort srt now iterate over a different (likely smaller domain)
    // - function values of sort srt still need to passed through the ``disappearing'' elim_f

    unsigned var = 0; // ... var will fly linearly through all this
    for(unsigned f=0; f<env.signature->functions();f++){
      ASS_EQ(var,_f_offsets[f]);
      Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* sig = symb->fnType();
      unsigned arity = symb->arity();

      // cout << "f = " << f << " arity= " << arity << endl;

      DArray<unsigned> args(arity); // ... args will respect the table encoding
      DArray<unsigned> old_args(arity);
      for(unsigned i=0;i<arity;i++){ args[i]=1; }

      for(;;) {
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        unsigned old_var = args2var(old_args,old_sizes,old_f_offsets,f,sig);
        unsigned old_res = old_f_interpretation[old_var];

        if (old_res) { // eliminated symbols don't have reasonable values
          unsigned res_srt = sig->result().term()->functor();
          unsigned res = (res_srt == srt) ?
                            // need to first pass old_res through elim_f, before mapping to the new domain
                            old_to_new.get(old_f_interpretation[old_f_offsets[elim_f]+old_res-1]) :
                            old_res;

          _f_interpretation[var] = res;

          if (arity==0 && !symb->introduced() && sortRepr[res_srt][res] == -1){
            sortRepr[res_srt][res]=f;
          }
        }

        // move var
        var++;
        // increase args
        unsigned i;
        for(i=0;i<arity;i++) {
          args[i]++;
          if(args[i] <= _sizes[sig->arg(i).term()->functor()]){
            break;
          }
          args[i]=1;
        }
        if (i == arity) {
          break;
        }
      }
    }

    var = 0; // ... var will fly linearly through all this again (for the predicates)
    for(unsigned p=1; p<env.signature->predicates();p++){
      ASS_EQ(var,_p_offsets[p]);
      Signature::Symbol* symb = env.signature->getPredicate(p);
      OperatorType* sig = symb->predType();
      unsigned arity = symb->arity();

      // cout << "p = " << p << " arity= " << arity << endl;

      DArray<unsigned> args(arity); // ... args will respect the table encoding
      DArray<unsigned> old_args(arity);
      for(unsigned i=0;i<arity;i++){ args[i]=1; }

      for(;;) {
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        unsigned old_var = args2var(old_args,old_sizes,old_p_offsets,p,sig);
        char old_res = old_p_interpretation[old_var];

        _p_interpretation[var++] = old_res; // no change for predicates

        // increase args
        unsigned i;
        for(i=0;i<arity;i++) {
          args[i]++;
          if(args[i] <= _sizes[sig->arg(i).term()->functor()]){
            break;
          }
          args[i]=1;
        }
        if (i == arity) {
          break;
        }
      }
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
      unsigned var = _p_offsets[elim_p];
      for(unsigned j = 1; j<=origSize; j++) {
        char res = _p_interpretation[var++];
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
    auto old_f_offsets        = std::move(_f_offsets);
    auto old_f_interpretation = std::move(_f_interpretation);
    auto old_p_offsets        = std::move(_p_offsets);
    auto old_p_interpretation = std::move(_p_interpretation);
    auto old_sizes = _sizes.clone();

    // update size of the affected sort
    _sizes[srt] = newSize;
    // cout << "origSize = " << origSize << " --> newSize = " << newSize << endl;

    initTables();

    // every function and predicate need to get reencoded
    // - arguments of sort srt now iterate over a different (likely smaller domain)

    unsigned var = 0; // ... var will fly linearly through all this
    for(unsigned f=0; f<env.signature->functions();f++){
      ASS_EQ(var,_f_offsets[f]);
      Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* sig = symb->fnType();
      unsigned arity = symb->arity();

      // cout << "  f = " << f << " arity= " << arity << " of name " << symb->name() << endl;
      // cout << "->usageCnt() == " << symb->usageCnt() << endl;

      DArray<unsigned> args(arity); // ... args will respect the table encoding
      DArray<unsigned> old_args(arity);
      for(unsigned i=0;i<arity;i++){ args[i]=1; }

      for(;;) {
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        unsigned old_var = args2var(old_args,old_sizes,old_f_offsets,f,sig);
        unsigned old_res = old_f_interpretation[old_var];

        if (old_res) { // eliminated symbols don't have reasonable values
          unsigned res_srt = sig->result().term()->functor();
          // this should be stipulated by the extra sort-predicate axioms
          ASS(res_srt != srt || old_p_interpretation[old_p_offsets[elim_p]+old_res-1] == INTP_TRUE)

          unsigned res = (res_srt == srt) ? old_to_new.get(old_res) : old_res;
          _f_interpretation[var] = res;

          if (arity==0 && !symb->introduced() && sortRepr[res_srt][res] == -1) {
            sortRepr[res_srt][res]=f;
          }
        }

        // move var
        var++;
        // increase args
        unsigned i;
        for(i=0;i<arity;i++) {
          args[i]++;
          if(args[i] <= _sizes[sig->arg(i).term()->functor()]){
            break;
          }
          args[i]=1;
        }
        if (i == arity) {
          break;
        }
      }
    }

    var = 0; // ... var will fly linearly through all this again (for the predicates)
    for(unsigned p=1; p<env.signature->predicates();p++){
      ASS_EQ(var,_p_offsets[p]);
      Signature::Symbol* symb = env.signature->getPredicate(p);
      OperatorType* sig = symb->predType();
      unsigned arity = symb->arity();

      // cout << "p = " << p << " arity= " << arity << endl;

      DArray<unsigned> args(arity); // ... args will respect the table encoding
      DArray<unsigned> old_args(arity);
      for(unsigned i=0;i<arity;i++){ args[i]=1; }

      for(;;) {
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        unsigned old_var = args2var(old_args,old_sizes,old_p_offsets,p,sig);
        unsigned old_res = old_p_interpretation[old_var];

        _p_interpretation[var++] = old_res; // no change for predicates

        // increase args
        unsigned i;
        for(i=0;i<arity;i++) {
          args[i]++;
          if(args[i] <= _sizes[sig->arg(i).term()->functor()]){
            break;
          }
          args[i]=1;
        }
        if (i == arity) {
          break;
        }
      }
    }
  }
}

void FiniteModelMultiSorted::restoreEliminatedFunDef(Problem::FunDef* fd)
{
  unsigned f = fd->_head->functor();
  unsigned arity = env.signature->functionArity(f);

  DArray<int> vars(arity);
  for(unsigned i=0;i<arity;i++){
    ASS(fd->_head->nthArgument(i)->isVar());
    vars[i] = fd->_head->nthArgument(i)->var();
  }

  static DArray<unsigned> args;
  args.ensure(arity);
  static DHMap<unsigned,unsigned> subst;
  subst.reset();
  // start with all 1s
  for(unsigned i=0;i<arity;i++){
    args[i]=1;
    subst.set(vars[i],args[i]);
  }

  OperatorType* ot = env.signature->getFunction(f)->fnType();
  for(;;) {
    unsigned val = evaluateTerm(TermList(fd->_body),subst);
    addFunctionDefinition(f,args,val);

    unsigned i;
    for(i=0;i<arity;i++) {
      args[i]++;
      if(args[i] <= _sizes[ot->arg(i).term()->functor()]) {
        subst.set(vars[i],args[i]); // update subst with the inc
        break;
      }
      args[i]=1;
      subst.set(vars[i],args[i]); // update subst with the dec
    }
    if (i == arity) {
      break;
    }
  }
}

void FiniteModelMultiSorted::restoreImplicitlyEliminatedFun(unsigned f)
{
  unsigned arity = env.signature->functionArity(f);

  static DArray<unsigned> args;
  args.ensure(arity);
  // start with all 1s
  for(unsigned i=0;i<arity;i++){ args[i]=1; }

  OperatorType* ot = env.signature->getFunction(f)->fnType();
  for(;;) {
    addFunctionDefinition(f,args,1);

    unsigned i;
    for(i=0;i<arity;i++) {
      args[i]++;
      if(args[i] <= _sizes[ot->arg(i).term()->functor()]) {
        break;
      }
      args[i]=1;
    }
    if (i == arity) {
      break;
    }
  }
}

void FiniteModelMultiSorted::restoreEliminatedPredDef(Problem::PredDef* pd)
{
  unsigned p = pd->_head->functor();
  unsigned arity = env.signature->predicateArity(p);

  DArray<int> vars(arity);
  for(unsigned i=0;i<arity;i++){
    ASS(pd->_head->nthArgument(i)->isVar());
    vars[i] = pd->_head->nthArgument(i)->var();
  }

  static DArray<unsigned> args;
  args.ensure(arity);
  static DHMap<unsigned,unsigned> subst;
  subst.reset();
  // start with all 1s
  for(unsigned i=0;i<arity;i++){
    args[i]=1;
    subst.set(vars[i],args[i]);
  }

  OperatorType* ot = env.signature->getPredicate(p)->fnType();
  for(;;) {
    bool val = (evaluateFormula(pd->_body,subst) == pd->_head->isPositive());
    addPredicateDefinition(p,args,val);

    unsigned i;
    for(i=0;i<arity;i++) {
      args[i]++;
      if(args[i] <= _sizes[ot->arg(i).term()->functor()]) {
        subst.set(vars[i],args[i]); // update subst with the inc
        break;
      }
      args[i]=1;
      subst.set(vars[i],args[i]); // update subst with the dec
    }
    if (i == arity) {
      break;
    }
  }
}

void FiniteModelMultiSorted::restoreImplicitlyEliminatedPred(unsigned p)
{
  unsigned arity = env.signature->predicateArity(p);

  static DArray<unsigned> args;
  args.ensure(arity);
  // start with all 1s
  for(unsigned i=0;i<arity;i++){ args[i]=1;}

  OperatorType* ot = env.signature->getPredicate(p)->fnType();
  for(;;) {
    unsigned var = args2var(args,_sizes,_p_offsets,p,env.signature->getPredicate(p)->predType());
    if (_p_interpretation[var] == INTP_UNDEF) // default only conditionally (some flips may have already been done)
      _p_interpretation[var] = INTP_FALSE;

    unsigned i;
    for(i=0;i<arity;i++) {
      args[i]++;
      if(args[i] <= _sizes[ot->arg(i).term()->functor()]) {
        break;
      }
      args[i]=1;
    }
    if (i == arity) {
      break;
    }
  }
}

void FiniteModelMultiSorted::restoreGlobalPredicateFlip(Problem::GlobalFlip* gf)
{
  unsigned p = gf->_pred;
  unsigned arity = env.signature->predicateArity(p);

  static DArray<unsigned> args;
  args.ensure(arity);
  // start with all 1s
  for(unsigned i=0;i<arity;i++){ args[i]=1;}

  OperatorType* ot = env.signature->getPredicate(p)->fnType();
  for(;;) {
    unsigned var = args2var(args,_sizes,_p_offsets,p,env.signature->getPredicate(p)->predType());
    if (_p_interpretation[var] == INTP_TRUE) {
      _p_interpretation[var] = INTP_FALSE;
    } else { // includes INTP_UNDEF, which is implicitly false
      _p_interpretation[var] = INTP_TRUE;
    }

    unsigned i;
    for(i=0;i<arity;i++) {
      args[i]++;
      if(args[i] <= _sizes[ot->arg(i).term()->functor()]) {
        break;
      }
      args[i]=1;
    }
    if (i == arity) {
      break;
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
    static DArray<unsigned> args;
    args.ensure(arity);
    // start with all 1s
    for(unsigned i=0;i<arity;i++){
      args[i]=1;
      subst.set(vars[i],args[i]);
    }

    unsigned p = cf->_val->functor();
    ASS_NEQ(p,0) // equality cannot be flipped!
    unsigned p_arity = env.signature->predicateArity(p);
    static DArray<unsigned> inner_args;
    inner_args.ensure(p_arity);

    for(;;) {
      if (evaluateFormula(cf->_cond,subst) != cf->_neg) {
        // cout << " do the flip for " << args << endl;
        // do the flip
        for(unsigned j=0;j<p_arity;j++){
          inner_args[j] = evaluateTerm(*cf->_val->nthArgument(j),subst);
        }
        unsigned var = args2var(inner_args,_sizes,_p_offsets,p,env.signature->getPredicate(p)->predType());
        ASS_L(var, _p_interpretation.size());

        char before = _p_interpretation[var];
        char after = (cf->_val->isPositive() ? INTP_TRUE : INTP_FALSE);
        // cout << " before " << (unsigned)_p_interpretation[var] << endl;
        _p_interpretation[var] = after;
        // cout << "  after " << (unsigned)_p_interpretation[var] << endl;
        flipped |= (before != after);
      }

      unsigned i;
      for(i=0;i<arity;i++) {
        args[i]++;
        if(args[i] <= _sizes[sorts[i]]) {
          subst.set(vars[i],args[i]); // update subst with the inc
          break;
        }
        args[i]=1;
        subst.set(vars[i],args[i]); // update subst with the dec
      }
      if (i == arity) {
        break;
      }
    }
  } while (cf->_fixedPoint && flipped);
  // cout << endl;
}

void FiniteModelMultiSorted::restoreEliminatedDefinitions(Kernel::Problem* prob)
{
  auto ii = prob->interferences.iter(); // LIFO is the key here!
  while (ii.hasNext()) {
    Problem::Interference* i = ii.next();
    switch (i->_kind) {
      case Problem::IntereferenceKind::FUN_DEF:
        restoreEliminatedFunDef(static_cast<Problem::FunDef*>(i));
        break;
      case Problem::IntereferenceKind::PRED_DEF:
        restoreEliminatedPredDef(static_cast<Problem::PredDef*>(i));
        break;
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

bool FiniteModelMultiSorted::evaluate(Unit* unit, bool expectingPartial)
{
  Formula* formula = 0;
  if(unit->isClause()){
    Clause* clause = unit->asClause();
    formula = Formula::fromClause(clause);
  }
  else{
    FormulaUnit* fu = static_cast<FormulaUnit*>(unit);
    fu = Rectify::rectify(fu);
    fu = SimplifyFalseTrue::simplify(fu);
    fu = Flattening::flatten(fu);
    formula = fu->getFormula();
  }

  formula = partialEvaluate(formula);
  formula = SimplifyFalseTrue::simplify(formula);

  DHMap<unsigned,unsigned> subst;
  bool res = evaluateFormula(formula,subst);
  if (!expectingPartial && (_implicitlyEliminatedFunctions.size() > 0 || _implicitlyEliminatedPredicates.size() > 0)) {
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
      VList* vs = formula->vars();
      SList* ss = formula->sorts(); // let's assume first these are filled

      // cout << "will do FORALL/EXISTS for " << formula->toString() << endl;

      unsigned arity = VList::length(vs);
      DArray<unsigned> args;
      DArray<unsigned> old_vals;
      DArray<unsigned> sorts;
      args.ensure(arity);
      old_vals.ensure(arity);
      sorts.ensure(arity);

      // start with all 1s, update subst, store old_vals, figure out sorts
      for(unsigned i=0;i<arity;i++){
        unsigned var = vs->head();
        vs = vs->tail();
        TermList srt;
        if (ss) {
          srt = ss->head();
          ss = ss->tail();
        } else {
          if(!SortHelper::tryGetVariableSort(var,formula,srt)){
            USER_ERROR("Failed to get sort of "+Lib::Int::toString(var)+" in "+formula->toString());
          }
        }
        sorts[i] = srt.term()->functor();

        old_vals[i] = subst.get(var,0);
        args[i]=1;
        subst.set(var,args[i]);
      }

      bool res;
      bool early = false;
      for(;;) {
        res = evaluateFormula(formula->qarg(),subst);

        if((isForall && !res) || (!isForall && res)) {
          early = true;

          // cout << "early for " << args << endl;
          // cout << "subst was " << subst << endl;

          break;
        }

        unsigned i;
        VList* vs = formula->vars();
        for(i=0;i<arity;i++) {
          unsigned var = vs->head();
          vs = vs->tail();
          args[i]++;
          if(args[i] <= _sizes[sorts[i]]) {
            subst.set(var,args[i]); // update subst with the inc
            break;
          }
          args[i]=1;
          subst.set(var,args[i]); // update subst with the dec
        }
        if (i == arity) {
          break;
        }
      }

      // undo the bindings in subst
      vs = formula->vars();
      for(unsigned i=0;i<arity;i++){
        unsigned var = vs->head();
        vs = vs->tail();

        subst.set(var,old_vals[i]);
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

/**
 *
 * TODO: This is recursive, which could be problematic in the long run
 *
 */
bool FiniteModelMultiSorted::evaluateOld(Formula* formula,unsigned depth)
{
#if DEBUG_MODEL
  for(unsigned i=0;i<depth;i++){ cout << "."; }
  cout << "Evaluating..." << formula->toString() << endl;
#endif

  bool isAnd = false;
  bool isImp = false;
  bool isXor = false;
  bool isForall = false;
  switch(formula->connective()){
    // If it's a literal evaluate that
    case LITERAL:
    {
      Literal* lit = formula->literal();
      if(!lit->ground()){
        USER_ERROR("Was not expecting free variables in "+formula->toString());
      }
      return evaluateGroundLiteral(lit);
    }

    // Expand the standard ones
    case FALSE:
      return false;
    case TRUE:
      return true;
    case NOT:
      return !evaluateOld(formula->uarg(),depth+1);
    case AND:
      isAnd=true;
    case OR:
      {
        FormulaList* args = formula->args();
        FormulaList::Iterator fit(args);
        while(fit.hasNext()){
          Formula* arg = fit.next();
          bool res = evaluateOld(arg,depth+1);
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
      bool left_res = evaluateOld(left,depth+1);
      if(isImp && !left_res) return true;
      bool right_res = evaluateOld(right,depth+1);

#if DEBUG_MODEL
      cout << "left_res is " << left_res << ", right_res is " << right_res << endl;
#endif

      if(isImp) return !left_res || right_res;
      if(isXor) return left_res != right_res;
      return left_res == right_res; // IFF
    }

    // Expand quantifications
    case FORALL:
     isForall = true;
    case EXISTS:
    {
     VList* vs = formula->vars();
     int var = vs->head();

     //cout << "Quant " << isForall << " with " << var << endl;

     Formula* next = 0;
     if(vs->tail()) next = new QuantifiedFormula(formula->connective(),vs->tail(),0,formula->qarg());
     else next = formula->qarg();

     TermList srt;
     if(!SortHelper::tryGetVariableSort(var,formula,srt)){
       USER_ERROR("Failed to get sort of "+Lib::Int::toString(var)+" in "+formula->toString());
     }

     unsigned srtU = srt.term()->functor();
     for(unsigned c=1;c<=_sizes[srtU];c++){
       Substitution s;
       s.bindUnbound(var,getDomainConstant(c,srtU));
       Formula* next_sub = SubstHelper::apply(next,s);
       next_sub = SimplifyFalseTrue::simplify(next_sub);
       next_sub = Flattening::flatten(next_sub);

       bool res = evaluateOld(next_sub,depth+1);

       //TODO try and limit memory issues!
       //     ideally delete the bits introduced by the application of SubstHelper::apply
       //if(next_sub!=next) next_sub->destroy();

       if(isForall && !res) return false;
       if(!isForall && res) return true;
     }

     return isForall;
    }
    default:
      USER_ERROR("Cannot evaluate " + formula->toString() + ", not supported");
  }

  NOT_IMPLEMENTED;
  return false;
}

    /**
     *
     * TODO: This is recursive, which could be problematic in the long run
     *
     */
    Formula* FiniteModelMultiSorted::partialEvaluate(Formula* formula)
    {
#if DEBUG_MODEL
        for(unsigned i=0;i<depth;i++){ cout << "."; }
        cout << "Evaluating..." << formula->toString() << endl;
#endif

        switch(formula->connective()){
                case LITERAL:
            {
                Literal* lit = formula->literal();
                if(!lit->ground()){
                    return formula;
                }
                bool evaluated = evaluateGroundLiteral(lit);
                return evaluated ? Formula::trueFormula() : Formula::falseFormula();
            }

                case FALSE:
                case TRUE:
                    return formula;
                case NOT:
                {
                  Formula* inner = partialEvaluate(formula->uarg());
                  return new NegatedFormula(inner);
                }
                case AND:
                case OR:
            {
                FormulaList* args = formula->args();
                FormulaList* newArgs = 0;
                FormulaList::Iterator fit(args);
                while(fit.hasNext()){
                    Formula* newArg = partialEvaluate(fit.next());
                    FormulaList::push(newArg,newArgs);
                }
                return new JunctionFormula(formula->connective(),newArgs);
            }

                case IMP:
                case XOR:
                case IFF:
            {
                Formula* left = formula->left();
                Formula* right = formula->right();
                Formula* newLeft = partialEvaluate(left);
                Formula* newRight = partialEvaluate(right);

                return new BinaryFormula(formula->connective(),newLeft,newRight);
            }

                case FORALL:
                case EXISTS:
            {
                VList* vs = formula->vars();
                Formula* inner  = formula->qarg();
                Formula* newInner = partialEvaluate(inner);
                return new QuantifiedFormula(formula->connective(),vs,0,newInner);
            }
            default:
                USER_ERROR("Cannot evaluate " + formula->toString() + ", not supported");
        }

        NOT_IMPLEMENTED;
        return 0;
    }


}
