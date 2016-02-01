/**
 * @file FunctionRelationshipInference.cpp
 * Implements class FunctionRelationshipInference.
 *
 */

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VString.hpp"
    
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Connective.hpp" 
#include "Kernel/Inference.hpp"
#include "Kernel/MainLoop.hpp"                      

#include "Saturation/SaturationAlgorithm.hpp"
    
#include "Shell/UIHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/CNF.hpp"
#include "Shell/NNF.hpp" 

#include "FunctionRelationshipInference.hpp"

namespace FMB
{
using namespace Shell;

void FunctionRelationshipInference::findFunctionRelationships(ClauseIterator clauses, 
                                                              DHMap<unsigned,Stack<unsigned>>& injective,
                                                              DHMap<unsigned,Stack<unsigned>>& surjective){
  CALL("FunctionRelationshipInference::findFunctionRelationships");

  ClauseList* checkingClauses = getCheckingClauses();

  ClauseIterator cit = pvi(getConcatenatedIterator(clauses,pvi(ClauseList::Iterator(checkingClauses))));

  Problem prb(cit,false);
  Options opt;

  SaturationAlgorithm* salg = SaturationAlgorithm::createFromOptions(prb,opt);
  MainLoopResult sres(salg->run());

}

ClauseList* FunctionRelationshipInference::getCheckingClauses()
{
  CALL("FunctionRelationshipInference::getCheckingClauses");

  ClauseList* newClauses = 0;

  unsigned initial_functions = env.signature->functions();
  for(unsigned f=0; f < initial_functions; f++){

    FunctionType* ftype = env.signature->getFunction(f)->fnType();
    unsigned ret_srt = ftype->result();
    unsigned arity = env.signature->functionArity(f);

    bool different_sorted=false;
    for(unsigned i=0;i<arity;i++){
      if(ret_srt != ftype->arg(i)){
        different_sorted=true;
        break;
      }
    }
    if(!different_sorted) continue;

    TermList x(0,false);
    TermList y(1,false);


    // ignore constants
    if(arity==0) continue;

    // For unary functions it's straight forward
    if(arity == 1){
      unsigned arg_srt = ftype->arg(0);
      TermList fx(Term::create1(f,x));
      TermList fy(Term::create1(f,y));
      addClaimForFunction(x,y,fx,fy,f,arg_srt,ret_srt,0,newClauses);
    }
    else{
    // Otherwise we need to existentially quantify over some of the variables
    // First go, let's use each argument as a singleton variable once
    // i.e. f(x,_,_), f(_,x,_), f(_,_,x)
    // and ignore cases like f(x,x,_)
      Formula::VarList* existential = Formula::VarList::empty();
      for(unsigned i=0;i<arity-1;i++){
        existential = new Formula::VarList(i+2,existential);
      }

      for(unsigned i=0;i<arity;i++){
        TermList xargs[arity];
        TermList yargs[arity];

        unsigned v=2;
        for(unsigned j=0;j<arity;j++){
          if(i==j){
            xargs[j]=x;
            yargs[j]=y;
          }
          else{
            xargs[j]=TermList(v,false);
            yargs[j]=TermList(v,false);
            v++;
          }
        }
        TermList fx(Term::create(f,arity,xargs));
        TermList fy(Term::create(f,arity,yargs));

        unsigned arg_srt = ftype->arg(i);
        addClaimForFunction(x,y,fx,fy,f,arg_srt,ret_srt,existential,newClauses);
      }
    }

  }
  return newClauses;

}

void FunctionRelationshipInference::addClaimForFunction(TermList x, TermList y, TermList fx, TermList fy,
                                               unsigned fname,
                                               unsigned arg_srt, unsigned ret_srt, Formula::VarList* existential,
                                               ClauseList*& newClauses)
{
    CALL("FunctionRelationshipInference::addClaimForFunction");

    Formula::VarList* xy = new Formula::VarList(0,new Formula::VarList(1));

    Formula* eq_fxfy = new AtomicFormula(Literal::createEquality(true,fx,fy,ret_srt));
    Formula* eq_xy = new AtomicFormula(Literal::createEquality(true,x,y,arg_srt));

    Formula* injective = 
      new QuantifiedFormula(FORALL,xy,0,new BinaryFormula(IMP,eq_fxfy,eq_xy));

    Formula* surjective =
      new QuantifiedFormula(FORALL, new Formula::VarList(0),0,
      new QuantifiedFormula(EXISTS, new Formula::VarList(1),0,
      new AtomicFormula(Literal::createEquality(true,fx,y,ret_srt))));


    if(existential){
      injective  = new QuantifiedFormula(EXISTS, existential, 0, injective);
      surjective = new QuantifiedFormula(EXISTS, existential, 0, surjective);
    }
    // Add names (true/false relates to being injective or not i.e. surjective)
    injective = new BinaryFormula(IFF,injective,getName(fname,true));
    surjective = new BinaryFormula(IFF,surjective,getName(fname,false));

    addClaim(injective,newClauses);
    addClaim(surjective,newClauses);
}

void FunctionRelationshipInference::addClaim(Formula* conjecture, ClauseList*& newClauses)
{
    CALL("FunctionRelationshipInference::addClaim");
    
    Formula* negated_conjecture = new NegatedFormula(conjecture);

    FormulaUnit* conjecture_fu = new FormulaUnit(conjecture,
                                 new Inference(Inference::INPUT),Unit::CONJECTURE); //TODO create new Inference kind?
    FormulaUnit* fu = new FormulaUnit(negated_conjecture,
                      new Inference1(Inference::NEGATED_CONJECTURE,conjecture_fu),
                      Unit::CONJECTURE);

    fu = Rectify::rectify(fu);
    fu = NNF::ennf(fu);
    fu = Flattening::flatten(fu);
    fu = Skolem::skolemise(fu);
    fu = Flattening::flatten(fu);

    Stack<Clause*> cls;
    CNF cnf;
    cnf.clausify(fu,cls);

    ClauseList::pushFromIterator(Stack<Clause*>::Iterator(cls),newClauses);
}

Formula* FunctionRelationshipInference::getName(unsigned functionName, bool injective)
{
    CALL("FunctionRelationshipInference::getName");

    vstring name = (injective ? "injective" : "surjective");
    name += "Label";
    unsigned label= env.signature->addFreshPredicate(0,name.c_str());

    if(injective){
      injectiveMap.insert(label,functionName);
    }
    else{
      surjectiveMap.insert(label,functionName);
    }

    return new AtomicFormula(Literal::create(label,0,true,false,0)); 
}

}
