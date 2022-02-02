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

#include <cmath>
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

using namespace Lib;
using namespace Kernel;
using namespace Shell;

FiniteModelMultiSorted::FiniteModelMultiSorted(DHMap<unsigned,unsigned> sizes) : 
   _sizes(sizes), _isPartial(false)
{
  CALL("FiniteModelMultiSorted::FiniteModelMultiSorted");

  (void)_isPartial; // to suppress unused warning

  f_offsets.ensure(env.signature->functions());
  p_offsets.ensure(env.signature->predicates());

  // generate offsets per function for indexing f_interpreation
  // see addFunctionDefinition for how the offset is used to compute
  // the actual index
  unsigned offsets=1;
  for(unsigned f=0; f<env.signature->functions();f++){
    unsigned arity=env.signature->functionArity(f);
    f_offsets[f]=offsets;

    OperatorType* sig = env.signature->getFunction(f)->fnType();
    unsigned s = sig->result().term()->functor();
    unsigned add = _sizes.get(s);
    for(unsigned i=0;i<arity;i++){ 
      s = sig->arg(i).term()->functor();
      add*= _sizes.get(s); 
    }
    
    ASS(UINT_MAX - add > offsets);
    offsets += add;
  }
  f_interpretation.expand(offsets+1,0);
  // can restart for predicates as indexing p_interepration instead
  offsets=1;
  for(unsigned p=1; p<env.signature->predicates();p++){
    unsigned arity=env.signature->predicateArity(p);
    p_offsets[p]=offsets;

    OperatorType* sig = env.signature->getPredicate(p)->predType();
    unsigned add = 1;

    for(unsigned i=0;i<arity;i++){ 
      unsigned s = sig->arg(i).term()->functor();
      int mult = _sizes.get(s); 
      ASS(mult>0);
      add*= (mult>0 ? mult : 1);
    }

    ASS(UINT_MAX - add > offsets);
    offsets += add;
  }
  p_interpretation.expand(offsets+1,0);

  sortRepr.ensure(env.signature->typeCons());
  for(unsigned s=0;s<env.signature->typeCons();s++){
    sortRepr[s].ensure(_sizes.get(s)+1);
    for(unsigned i=0;i<=_sizes.get(s);i++){
      sortRepr[s][i] = -1;
    }
  }
}

void FiniteModelMultiSorted::addConstantDefinition(unsigned f, unsigned res)
{
  CALL("FiniteModelMultiSorted::addConstantDefinition");
  static const DArray<unsigned> empty(0);
  addFunctionDefinition(f,empty,res);
}

void FiniteModelMultiSorted::addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res)
{
  CALL("FiniteModelMultiSorted::addFunctionDefinition");

  ASS_EQ(env.signature->functionArity(f),args.size());

  if(env.signature->functionArity(f)==0 && !env.signature->getFunction(f)->introduced()){
    TermList srt = env.signature->getFunction(f)->fnType()->result();
    unsigned srtU = srt.term()->functor();
    if(sortRepr[srtU][res] == -1){
      //cout << "Rep " << env.signature->functionName(f) << " for ";
      //cout << env.sorts->sortName(srt) << " and " << res << endl;
      sortRepr[srtU][res]=f;
    }
  } 

  unsigned var = f_offsets[f];
  unsigned mult = 1;
  OperatorType* sig = env.signature->getFunction(f)->fnType();
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    unsigned s = sig->arg(i).term()->functor();
    mult *= _sizes.get(s);
  }

  //TODO should be a zero array, should check if previously assigned
  //     check consistency and only update coverage if not defined already
  
  ASS_L(var, f_interpretation.size());
  f_interpretation[var] = res;

  unsigned previous = 0;
  _functionCoverage.find(f,previous);
  _functionCoverage.insert(f,previous+1);

}

void FiniteModelMultiSorted::addPropositionalDefinition(unsigned p, bool res)
{
  CALL("FiniteModelMultiSorted::addPropositionalDefinition");
  
  static const DArray<unsigned> empty(0);
  addPredicateDefinition(p,empty,res);
}

void FiniteModelMultiSorted::addPredicateDefinition(unsigned p, const DArray<unsigned>& args, bool res)
{
  CALL("FiniteModelMultiSorted::addPredicateDefinition");

  ASS_EQ(env.signature->predicateArity(p),args.size());

  //cout << "addPredicateDefinition for " << p << "(" << env.signature->predicateName(p) << ")" << endl;

  unsigned var = p_offsets[p];
  unsigned mult = 1;
  OperatorType* sig = env.signature->getPredicate(p)->predType();
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    unsigned s = sig->arg(i).term()->functor();
    mult *=_sizes.get(s);
  }

  ASS_L(var, p_interpretation.size());
  p_interpretation[var] = (res ? 2 : 1);

  unsigned previous = 0;
  _predicateCoverage.find(p,previous);
  _predicateCoverage.insert(p,previous+1);
}

bool FiniteModelMultiSorted::isPartial()
{
  CALL("FiniteModelMultiSorted::isPartial");
  //TODO
  return true;
}

vstring FiniteModelMultiSorted::toString()
{
  CALL("FiniteModelMultiSorted::toString");

  vostringstream modelStm;

  bool printIntroduced = false;

  static DArray<DArray<vstring>> cnames;
  cnames.ensure(env.signature->typeCons());

  //Output sorts and their sizes 
  for(unsigned s=0;s<env.signature->typeCons();s++){

    unsigned size = _sizes.get(s);
    if(size==0) continue;

    vstring sortName = env.signature->typeConName(s);
    vstring sortNameLabel = (env.signature->isBoolCon(s)) ? "bool" : sortName;

    // Sort declaration
    modelStm << "tff(" << prepend("declare_", sortNameLabel) << ",type,"<<sortName<<":$tType)." <<endl;

    cnames[s].ensure(size+1);


    // Domain constant declarations
    for(unsigned i=1;i<=size;i++){
      modelStm << "tff(" << append(prepend("declare_", sortNameLabel), Int::toString(i).c_str()) << ",type,";
      int frep = sortRepr[s][i];
      vstring cname = "fmb_"+sortNameLabel+"_"+Lib::Int::toString(i);
      if(frep >= 0){
        cname = env.signature->functionName(frep);
      }
      cnames[s][i]=cname; 
      modelStm << cname << ":" << sortName << ")." << endl;
    }

    //Output domain
    modelStm << "tff(finite_domain,axiom," << endl;
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
    modelStm << "tff(distinct_domain,axiom," << endl;
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
    if(env.signature->getFunction(f)->usageCnt()==0) continue;
    unsigned arity = env.signature->functionArity(f);
    if(arity>0) continue;
    if(!printIntroduced && env.signature->getFunction(f)->introduced()) continue;
    vstring name = env.signature->functionName(f);
    unsigned res = f_interpretation[f_offsets[f]];
    TermList srtT = env.signature->getFunction(f)->fnType()->result();
    unsigned srt = srtT.term()->functor();
    vstring cname = cnames[srt][res];
    if(name == cname) continue;

    vstring sortName = env.signature->typeConName(srt);
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<":"<<sortName<<")."<<endl;
    if(res>0){ 
      modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<<" = " << cname << ")."<<endl;
    }
    else{
      modelStm << "% " << name << " undefined in model" << endl; 
    }
  }

  //Functions
  for(unsigned f=0;f<env.signature->functions();f++){
    if(env.signature->getFunction(f)->usageCnt()==0) continue;
    unsigned arity = env.signature->functionArity(f);
    if(arity==0) continue;
    if(!printIntroduced && env.signature->getFunction(f)->introduced()) continue;
    vstring name = env.signature->functionName(f);

    OperatorType* sig = env.signature->getFunction(f)->fnType();
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<": ";
    for(unsigned i=0;i<arity;i++){
      modelStm << sig->arg(i).toString();
      if(i+1 < arity) modelStm << " * ";
    }
    modelStm << " > " << sig->result().toString() << ")." << endl; 

    modelStm << "tff("<<prepend("function_", name)<<",axiom,"<<endl;

    unsigned offset = f_offsets[f];

    static DArray<unsigned> args;
    args.ensure(arity);
    for(unsigned i=0;i<arity;i++) args[i]=1;
    args[arity-1]=0;
    bool first=true;
fModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        TermList argST = sig->arg(i);
        unsigned argS = argST.term()->functor();
        if(args[i]==_sizes.get(argS)){
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
            mult *= _sizes.get(s);
          } 
          unsigned res = f_interpretation[var];

          if(res>0){
            if(!first){ modelStm << "         & " ; } 
            else{ modelStm << "           " ; }
            first=false;
          }
          else{
            modelStm << "%         ";
          }
          modelStm << name << "(";
          for(unsigned j=0;j<arity;j++){
            if(j!=0) modelStm << ",";
            TermList argSortT = sig->arg(j);
            unsigned argSort = argSortT.term()->functor(); 
            modelStm << cnames[argSort][args[j]];
          }
          if(res>0){
            TermList resultSortT = sig->result();
            unsigned resultSort = resultSortT.term()->functor();    
            modelStm << ") = " << cnames[resultSort][res] << endl;
          }
          else{
            modelStm << ") undefined in model" << endl;
          }
          goto fModelLabel;
        }
      }
      modelStm << endl << ")." << endl << endl;
  }

  //Propositions
  for(unsigned f=1;f<env.signature->predicates();f++){
    unsigned arity = env.signature->predicateArity(f);
    if(arity>0) continue;
    if(!printIntroduced && env.signature->getPredicate(f)->introduced()) continue;
    vstring name = env.signature->predicateName(f);
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<": $o).";
    unsigned res = p_interpretation[p_offsets[f]];
    if(res==2){
      modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<< ")."<<endl;
    }
    else if(res==1){
      modelStm << "tff("<<append(name,"_definition")<<",axiom,~"<<name<< ")."<<endl;
    }
    else{
      modelStm << "% " << name << " undefined" << endl;
    }
  }

//Predicates
  for(unsigned f=1;f<env.signature->predicates();f++){
    unsigned arity = env.signature->predicateArity(f);
    if(arity==0) continue;
    if(!printIntroduced && env.signature->getPredicate(f)->introduced()) continue;
    vstring name = env.signature->predicateName(f);

    OperatorType* sig = env.signature->getPredicate(f)->predType();
    modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<": ";
    for(unsigned i=0;i<arity;i++){
      TermList argST = sig->arg(i);
      unsigned argS = argST.term()->functor();      
      modelStm << env.signature->typeConName(argS);
      if(i+1 < arity) modelStm << " * ";
    }
    modelStm << " > $o )." << endl;

    modelStm << "tff("<<prepend("predicate_", name)<<",axiom,"<<endl;

    unsigned offset = p_offsets[f];

    static DArray<unsigned> args;
    args.ensure(arity);
    for(unsigned i=0;i<arity;i++) args[i]=1;
    args[arity-1]=0;
    bool first=true;
pModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){
        TermList argST = sig->arg(i);
        unsigned argS = argST.term()->functor();
        if(args[i]==_sizes.get(argS)){
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
            mult *= _sizes.get(s);
          }
          unsigned res = p_interpretation[var];
          if(res>0){
            if(!first){ modelStm << "         & " ; }
            else{ modelStm << "           " ; }
            first=false;
          }
          else{
            modelStm << "%         ";
          }
          if(res==1) modelStm << "~";
          modelStm << name << "(";
          for(unsigned j=0;j<arity;j++){
            if(j!=0) modelStm << ",";
            TermList argSortT = sig->arg(j);
            unsigned argSort = argSortT.term()->functor();
            modelStm << cnames[argSort][args[j]]; 
          }
          modelStm << ")";
          if(res==0){
            modelStm << " undefined in model";
          }
          modelStm << endl;
          goto pModelLabel;
        }
      }
      modelStm << endl << ")." << endl << endl;
  }



  return modelStm.str();
}

unsigned FiniteModelMultiSorted::evaluateGroundTerm(Term* term)
{
  CALL("FiniteModelMultiSorted::evaluate(Term*)");
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
  unsigned var = f_offsets[term->functor()];
  unsigned mult = 1;
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    unsigned s = sig->arg(i).term()->functor();
    mult *=_sizes.get(s);
  }
#if VDEBUG
  if((term->functor()+1)<f_offsets.size()) ASS_L(var,f_offsets[term->functor()+1]);
#endif
  ASS_L(var,f_interpretation.size());

  return f_interpretation[var];
}

bool FiniteModelMultiSorted::evaluateGroundLiteral(Literal* lit)
{
  CALL("FiniteModelMultiSorted::evaluate(Literal*)");
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
  unsigned var = p_offsets[lit->functor()];
  unsigned mult = 1;
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    unsigned s = sig->arg(i).term()->functor();
    mult *=_sizes.get(s);
  }  

#if VDEBUG
  if((lit->functor()+1)<p_offsets.size()) ASS_L(var,p_offsets[lit->functor()+1]);
#endif
  ASS_L(var,p_interpretation.size());

  unsigned res = p_interpretation[var];
#if DEBUG_MODEL
    cout << "res is " << res << " and polarity is " << lit->polarity() << endl; 
#endif

  if(res==0) 
    USER_ERROR("Could not evaluate "+lit->toString()+", probably a partial model");

  if(lit->polarity()) return (res==2);
  else return (res==1); 
}

bool FiniteModelMultiSorted::evaluate(Unit* unit)
{
  CALL("FiniteModelMultiSorted::evaluate(Unit*)");

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
  return evaluate(formula);
}

/**
 *
 * TODO: This is recursive, which could be problematic in the long run
 * 
 */
bool FiniteModelMultiSorted::evaluate(Formula* formula,unsigned depth)
{
  CALL("FiniteModelMultiSorted::evaluate(Formula*)");

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
      return !evaluate(formula->uarg(),depth+1);
    case AND:
      isAnd=true;
    case OR:
      {
        FormulaList* args = formula->args();
        FormulaList::Iterator fit(args);
        while(fit.hasNext()){
          Formula* arg = fit.next();
          bool res = evaluate(arg,depth+1);
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
      bool left_res = evaluate(left,depth+1);
      if(isImp && !left_res) return true;
      bool right_res = evaluate(right,depth+1);
      
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
     for(unsigned c=1;c<=_sizes.get(srtU);c++){
       Substitution s;
       s.bind(var,getDomainConstant(c,srtU));
       Formula* next_sub = SubstHelper::apply(next,s);
       next_sub = SimplifyFalseTrue::simplify(next_sub);
       next_sub = Flattening::flatten(next_sub); 
       
       bool res = evaluate(next_sub,depth+1);

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
        CALL("FiniteModelMultiSorted::partialEvaluate(Formula*)");
        
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
