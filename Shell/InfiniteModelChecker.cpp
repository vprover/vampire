/**
 * @file InfiniteModelChecker.cpp
 *
 * @since 28/01/2016 Manchester
 * @author Giles
 */

#include "Forwards.hpp"

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

#include "Saturation/ProvingHelper.hpp"

#include "UIHelper.hpp"
#include "Statistics.hpp"
#include "Skolem.hpp"
#include "Rectify.hpp"
#include "Flattening.hpp"
#include "CNF.hpp"
#include "NNF.hpp"

#include "InfiniteModelChecker.hpp"

namespace Shell{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;

void InfiniteModelChecker::doCheck(Problem& prb)
{
  CALL("InfiniteModelChecker::doCheck");

  // Add the checking clauses
  addCheckingClauses(prb);

  ProvingHelper::runVampireSaturation(prb, *env.options);

  if(env.statistics->terminationReason == Statistics::REFUTATION){
    cout << "Infinite Model Detected" << endl;
  }
  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

}


void InfiniteModelChecker::addCheckingClauses(Problem& prb)
{
  CALL("InfiniteModelChecker::addCheckingClauses");

  UnitList* newClauses = 0;

  // For each unary function f add the conjecture that f is injective and non-surjective
  // i.e.
  // (![X,Y] : (f(X)=f(Y) => X=Y)) & (?[Y]:![X]: f(X) != Y)

  unsigned initial_functions = env.signature->functions();
  for(unsigned f=0; f < initial_functions; f++){

    FunctionType* ftype = env.signature->getFunction(f)->fnType();
    unsigned ret_srt = ftype->result();
    TermList x(0,false);
    TermList y(1,false);

    unsigned arity = env.signature->functionArity(f);

    // ignore constants
    if(arity==0) continue;

    // For unary functions it's straight forward 
    if(arity == 1){
      unsigned arg_srt = ftype->arg(0);
      // srts must be the same!!
      if(ret_srt != arg_srt) continue;
      TermList fx(Term::create1(f,x));
      TermList fy(Term::create1(f,y));
      addClaimForFunction(x,y,fx,fy,arg_srt,ret_srt,0,newClauses);
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

        unsigned arg_srt = ftype->arg(i);
        // srts must be the same!!
        if(ret_srt != arg_srt) continue;

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

        addClaimForFunction(x,y,fx,fy,arg_srt,ret_srt,existential,newClauses);
      }
    }

  }
  prb.addUnits(newClauses);
}
    


void InfiniteModelChecker::addClaimForFunction(TermList x, TermList y, TermList fx, TermList fy, 
                                               unsigned arg_srt, unsigned ret_srt, Formula::VarList* existential, 
                                               UnitList*& newClauses)
{
    CALL("InfiniteModelChecker::addClaimForFunction");

    Formula::VarList* xy = new Formula::VarList(0,new Formula::VarList(1));

    Formula* eq_fxfy = new AtomicFormula(Literal::createEquality(true,fx,fy,ret_srt));
    Formula* eq_xy = new AtomicFormula(Literal::createEquality(true,x,y,arg_srt));

    Formula* injective =  
      new QuantifiedFormula(FORALL,xy,0,new BinaryFormula(IMP,eq_fxfy,eq_xy));

    Formula* nonsurjective =
      new QuantifiedFormula(EXISTS, new Formula::VarList(1),0,
      new QuantifiedFormula(FORALL, new Formula::VarList(0),0,
      new AtomicFormula(Literal::createEquality(false,fx,y,ret_srt))));

    
    Formula* conjecture = 
      new JunctionFormula(AND,new FormulaList(injective,new FormulaList(nonsurjective)));

    if(existential){
      conjecture = new QuantifiedFormula(EXISTS, existential, 0, conjecture);
    }

    Formula* negated_conjecture = new NegatedFormula(conjecture);

    FormulaUnit* conjecture_fu = new FormulaUnit(conjecture,
                                 new Inference(Inference::INFINOX_CLAIM),Unit::CONJECTURE);
    FormulaUnit* fu = new FormulaUnit(negated_conjecture,
                      new Inference1(Inference::NEGATED_CONJECTURE,conjecture_fu),
                      Unit::CONJECTURE); 

    // Important, need to rectify
    fu = Rectify::rectify(fu);
    fu = NNF::ennf(fu);
    fu = Flattening::flatten(fu);
    fu = Skolem::skolemise(fu);
    fu = Flattening::flatten(fu);

    Stack<Clause*> cls;
    CNF cnf;
    cnf.clausify(fu,cls);
    
    UnitList::pushFromIterator(Stack<Clause*>::Iterator(cls),newClauses);
} 


}
