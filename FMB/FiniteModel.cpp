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
 * @file FiniteModel.cpp
 * Defines class for finite models
 *
 * @since 26/09/2015 Manchester
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

#include "FiniteModel.hpp"

#define DEBUG_MODEL 0

namespace FMB{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

FiniteModel::FiniteModel(unsigned size) : _size(size), _isPartial(false)
{
  CALL("FiniteModel::FiniteModel");

  (void)_isPartial; // to suppress unused warning

  f_offsets.ensure(env.signature->functions());
  p_offsets.ensure(env.signature->predicates());

  // generate offsets per function for indexing f_interpreation
  // see addFunctionDefinition for how the offset is used to compute
  // the actual index
  unsigned offsets=1;
  for(unsigned f=0; f<env.signature->functions(); f++){
    unsigned arity=env.signature->functionArity(f);
    f_offsets[f]=offsets;
    unsigned add = pow(size,arity+1);
    ASS(UINT_MAX - add > offsets);
    offsets += add;
  }
  f_interpretation.expand(offsets+1,0);
  // can restart for predicates as indexing p_interepration instead
  offsets=1;
  for(unsigned p=1; p<env.signature->predicates();p++){
    unsigned arity=env.signature->predicateArity(p);
    p_offsets[p]=offsets;
    unsigned add = pow(size,arity+1);
    ASS(UINT_MAX - add > offsets);
    offsets += add;
  }
  p_interpretation.expand(offsets+1,0);

}

void FiniteModel::addConstantDefinition(unsigned f, unsigned res)
{
  CALL("FiniteModel::addConstantDefinition");
  static const DArray<unsigned> empty(0);
  addFunctionDefinition(f,empty,res);
}

void FiniteModel::addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res)
{
  CALL("FiniteModel::addFunctionDefinition");

  ASS_EQ(env.signature->functionArity(f),args.size());

  unsigned var = f_offsets[f];
  unsigned mult = 1;
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    mult *=_size;
  }

  //TODO should be a zero array, should check if previously assigned
  //     check consistency and only update coverage if not defined already
  
  ASS_L(var, f_interpretation.size());
  f_interpretation[var] = res;

  unsigned previous = 0;
  _functionCoverage.find(f,previous);
  _functionCoverage.insert(f,previous+1);

}

void FiniteModel::addPropositionalDefinition(unsigned p, bool res)
{
  CALL("FiniteModel::addPropositionalDefinition");
  
  static const DArray<unsigned> empty(0);
  addPredicateDefinition(p,empty,res);
}

void FiniteModel::addPredicateDefinition(unsigned p, const DArray<unsigned>& args, bool res)
{
  CALL("FiniteModel::addPredicateDefinition");

  ASS_EQ(env.signature->predicateArity(p),args.size());

  unsigned var = p_offsets[p];
  unsigned mult = 1;
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    mult *=_size;
  }

  ASS_L(var, p_interpretation.size());
  p_interpretation[var] = (res ? 2 : 1);

  unsigned previous = 0;
  _predicateCoverage.find(p,previous);
  _predicateCoverage.insert(p,previous+1);
}

bool FiniteModel::isPartial()
{
  CALL("FiniteModel::isPartial");
  //TODO
  return true;
}

vstring FiniteModel::toString()
{
  CALL("FiniteModel::toString");

  vostringstream modelStm;

  bool printIntroduced = false;

  //Output domain
  modelStm << "fof(finite_domain,axiom," << endl;
  modelStm << "      ! [X] : (" << endl;
  modelStm << "         ";
  for(unsigned i=1;i<=_size;i++){
  modelStm << "X = fmb" << i;
  if(i<_size) modelStm << " | ";
  if(i==_size) modelStm << endl;
  else if(i%5==0) modelStm << endl << "         ";
  }
  modelStm << "      ) )." <<endl;
  //Distinctness of domain
  modelStm << endl;
  if(_size>1){
  modelStm << "fof(distinct_domain,axiom," << endl;
  modelStm << "         ";
  unsigned c=0;
  for(unsigned i=1;i<=_size;i++){
    for(unsigned j=i+1;j<=_size;j++){
      c++;
      modelStm << "fmb"<<i<<" != fmb"<<j;
      if(!(i==_size-1 && j==_size)){
         modelStm << " & ";
         if(c%5==0){ modelStm << endl << "         "; }
      }
      else{ modelStm << endl; }
    }
  }
  modelStm << ")." << endl << endl;
  }

  //Constants
  for(unsigned f=0;f<env.signature->functions();f++){
    unsigned arity = env.signature->functionArity(f);
    if(arity>0) continue;
    if(!printIntroduced && env.signature->getFunction(f)->introduced()) continue;
    vstring name = env.signature->functionName(f);
    unsigned res = f_interpretation[f_offsets[f]];
    if(res>0){ 
      modelStm << "fof("<<name<<"_definition,axiom,"<<name<<" = fmb"<< res << ")."<<endl;
    }
    else{
      modelStm << "% " << name << " undefined in model" << endl; 
    }
  }

  //Functions
  for(unsigned f=0;f<env.signature->functions();f++){
    unsigned arity = env.signature->functionArity(f);
    if(arity==0) continue;
    if(!printIntroduced && env.signature->getFunction(f)->introduced()) continue;
    vstring name = env.signature->functionName(f);
    modelStm << "fof(function_"<<name<<",axiom,"<<endl;

    unsigned offset = f_offsets[f];

    static DArray<unsigned> args;
    args.ensure(arity);
    for(unsigned i=0;i<arity;i++) args[i]=1;
    args[arity-1]=0;
    bool first=true;
fModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(args[i]==_size){
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
            mult *= _size;
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
            modelStm << "fmb" << args[j];
          }
          if(res>0){
            modelStm << ") = fmb" <<res << endl;
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
    unsigned res = p_interpretation[p_offsets[f]];
    if(res==2){
      modelStm << "fof("<<name<<"_definition,axiom,"<<name<< ")."<<endl;
    }
    else if(res==1){
      modelStm << "fof("<<name<<"_definition,axiom,~"<<name<< ")."<<endl;
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
    modelStm << "fof(predicate_"<<name<<",axiom,"<<endl;

    unsigned offset = p_offsets[f];

    static DArray<unsigned> args;
    args.ensure(arity);
    for(unsigned i=0;i<arity;i++) args[i]=1;
    args[arity-1]=0;
    bool first=true;
pModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(args[i]==_size){
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
            mult *= _size;
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
            modelStm << "fmb" << args[j];
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

unsigned FiniteModel::evaluateGroundTerm(Term* term)
{
  CALL("FiniteModel::evaluate(Term*)");
  ASS(term->ground());

#if DEBUG_MODEL
  cout << "evaluating ground term " << term->toString() << endl;
  cout << "domain constant status " << isDomainConstant(term) << endl;
#endif  
  if(isDomainConstant(term)) return getDomainConstant(term);

  unsigned arity = env.signature->functionArity(term->functor());
  DArray<unsigned> args(arity);
  for(unsigned i=0;i<arity;i++){
    args[i] = evaluateGroundTerm(term->nthArgument(i)->term());
    if(args[i]==0) USER_ERROR("Could not evaluate "+term->toString());
  }

  unsigned var = f_offsets[term->functor()];
  unsigned mult = 1;
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    mult *=_size;
  }
#if VDEBUG
  if((term->functor()+1)<f_offsets.size()) ASS_L(var,f_offsets[term->functor()+1]);
#endif
  ASS_L(var,f_interpretation.size());

  return f_interpretation[var];
}

bool FiniteModel::evaluateGroundLiteral(Literal* lit)
{
  CALL("FiniteModel::evaluate(Literal*)");
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

  unsigned var = p_offsets[lit->functor()];
  unsigned mult = 1;
  for(unsigned i=0;i<args.size();i++){
    var += mult*(args[i]-1);
    mult *=_size;
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

bool FiniteModel::evaluate(Unit* unit)
{
  CALL("FiniteModel::evaluate(Unit*)");

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
bool FiniteModel::evaluate(Formula* formula,unsigned depth)
{
  CALL("FiniteModel::evaluate(Formula*)");

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

     for(unsigned c=1;c<=_size;c++){
       Substitution s;
       s.bind(var,getDomainConstant(c));
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
    Formula* FiniteModel::partialEvaluate(Formula* formula)
    {
        CALL("FiniteModel::partialEvaluate(Formula*)");
        
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
