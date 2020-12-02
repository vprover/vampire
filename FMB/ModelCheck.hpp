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
 * @file ModelCheck.hpp 
 * Defines checking of finite models 
 *
 * @since 6/10/2015 Manchester
 * @author Giles
 */

#ifndef __ModelCheck__
#define __ModelCheck__

#include "Lib/DHMap.hpp"
#include "Lib/Set.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"

#include "FiniteModel.hpp"


namespace FMB{

using namespace Lib;
using namespace Kernel;

class ModelCheck{

public:
static void doCheck(Problem*& prb)
{
  CALL("ModelCheck::doCheck");

  // find model size
  // looking for a domain axiom
  // Currently assume it is called 'finite_domain'
  // TODO search for something of the right shape
  unsigned modelSize = 0;
  Set<Term*> domainConstants;
  {
    UnitList::Iterator uit(prb->units());
    while(uit.hasNext()){
      Unit* u = uit.next();
      if(u->inputType()!= UnitInputType::MODEL_DEFINITION) continue;
      vstring name;
      ALWAYS(Parse::TPTP::findAxiomName(u,name));
      if(name == "finite_domain"){
        //cout << "Finite domain axiom found:" << endl << u->toString() << endl;
        // Set model size and domainConstants
        // And check it is a finite domain axiom
        if(u->isClause()){
          Clause* c = u->asClause();
          modelSize = c->length();
          int single_var = -1;
          for(unsigned i=0;i<c->length();i++){
            Literal* l = (*c)[i];
            checkIsDomainLiteral(l,single_var,domainConstants);
          }
        }else{
          Formula* formula = u->getFormula();
          if(formula->connective()!=Connective::FORALL) USER_ERROR("finite_domain is not a domain axiom");
          Formula* subformula = formula->qarg();
          if(subformula->connective()!=Connective::OR) USER_ERROR("finite_domain is not a domain axiom");
          FormulaList* args = subformula->args();
          FormulaList::Iterator fit(args);
          int single_var = -1;
          while(fit.hasNext()){
            modelSize++;
            Formula* arg = fit.next();
            if(arg->connective()!=Connective::LITERAL) USER_ERROR("finite_domain is not a domain axiom");
            Literal* l = arg->literal();
            checkIsDomainLiteral(l,single_var,domainConstants);
          }
        }
      }
    }
  }
  ASS_EQ(modelSize,(unsigned)domainConstants.size());
  cout << "Detected model of size " << modelSize << endl;
  cout << "Distinct domain assumed, domain elements are:" << endl;

  // number the domain constants
  DHMap<Term*,unsigned> domainConstantNumber;
  Set<Term*>::Iterator dit(domainConstants);
  unsigned count=1;
  while(dit.hasNext()){ 
    Term* con = dit.next();
    cout << con->toString() << endl; 
    domainConstantNumber.insert(con,count++); 
  }

  cout << "Loading model..." << endl;
  FiniteModel model(modelSize);

  {
    UnitList::Iterator uit(prb->units());
    while(uit.hasNext()){
      Unit* u = uit.next();
      if(u->inputType()!= UnitInputType::MODEL_DEFINITION) continue;
      vstring name;
      ALWAYS(Parse::TPTP::findAxiomName(u,name));
      if(name == "finite_domain" || name == "distinct_domain") continue;

      // All model formulas should be conjunctions of definitions
      // TODO allow for unit clause definitions in the future
      if(u->isClause()) USER_ERROR("Expecting model to use formulas i.e. fof");
      Formula* formula = u->getFormula();

      if(formula->connective()==Connective::NOT){
        Formula* inner = formula->uarg();
        if(inner->connective()==Connective::LITERAL){
          addDefinition(model,inner->literal(),true,domainConstants,domainConstantNumber);
        }
        else USER_ERROR("Unexpected negation in "+formula->toString());
      }
      else if(formula->connective()==Connective::LITERAL){
        addDefinition(model,formula->literal(),false,domainConstants,domainConstantNumber);
      }
      else{
        if(formula->connective()!=Connective::AND) 
          USER_ERROR("Expecting conjunction of definitions in model:\n"+formula->toString());
        FormulaList* defs = formula->args();
        FormulaList::Iterator fit(defs);
        while(fit.hasNext()){
          unsigned negated = false;
          Formula* def = fit.next();
          if(def->connective()==Connective::NOT){
            def = def->uarg();
            negated=true;
          }
          if(def->connective()!=Connective::LITERAL) USER_ERROR("Badly formed definition");
          Literal* lit = def->literal();
          addDefinition(model,lit,negated,domainConstants,domainConstantNumber);
        }
      }
    }
    cout << "Model loaded" << endl;
    cout << "Checking formulas..." << endl;
    {
      UnitList::Iterator uit(prb->units());
      while(uit.hasNext()){
        Unit* u = uit.next();
        if(u->inputType()== UnitInputType::MODEL_DEFINITION) continue;

        cout << "Checking " << u->toString() << "..." << endl;
        bool res = model.evaluate(u);
        cout << "Evaluates to " << (res ? "True" : "False") << endl;
      }
    }
  }
}

private:

static void checkIsDomainLiteral(Literal* l, int& single_var, Set<Term*>& domainConstants)
{
  CALL("ModelCheck::checkIsDomainLiteral");

            if(!l->isEquality()) USER_ERROR("finite_domain is not a domain axiom");

            // put var in left and constant in right
            TermList* left = l->nthArgument(0);
            TermList* right = l->nthArgument(1);
            if(right->isVar()){
              TermList* temp = left;left=right;right=temp;
            }
            if(right->isVar()) USER_ERROR("finite_domain is not a domain axiom");

            // store and check the single variable used
            if(single_var<0) single_var=left->var();
            if(left->var()!=(unsigned)single_var) USER_ERROR("finite_domain is not a domain axiom");

            // store and check the ground constant used
            Term* constant = right->term();
            unsigned f = constant->functor();
            if(env.signature->functionArity(f)!=0) USER_ERROR("finite_domain is not a domain axiom");
            if(domainConstants.contains(constant)) USER_ERROR("finite_domain is not a domain axiom");

            domainConstants.insert(constant);


}

static void addDefinition(FiniteModel& model,Literal* lit,bool negated,
                          Set<Term*>& domainConstants,
                          DHMap<Term*,unsigned>& domainConstantNumber)
{
  CALL("ModelCheck::addDefinition");

  if(lit->isEquality()){
          if(!lit->polarity() || negated) USER_ERROR("Cannot have negated function definition");
          // Defining a function or constant
          TermList* left = lit->nthArgument(0);
          TermList* right = lit->nthArgument(1);
          if(domainConstants.contains(left->term())){
            TermList* temp = left; left=right;right=temp;
          }

          if(domainConstants.contains(left->term())) 
            USER_ERROR("Cannot have equality between domain elements:\n"+lit->toString());
          unsigned res = domainConstantNumber.get(right->term());
          if(left->isVar()) USER_ERROR("Expect term on left of definition");
          Term* fun = left->term();
          unsigned f = fun->functor();
          unsigned arity = env.signature->functionArity(f);
          if(arity==0) model.addConstantDefinition(f,res);
          else{
            DArray<unsigned> args(arity);
            for(unsigned i=0;i<arity;i++){
              TermList* arg = fun->nthArgument(i);
              if(arg->isVar() || !domainConstants.contains(arg->term()))
                USER_ERROR("Expect term on left of definition to be grounded with domain constants");
              args[i] = domainConstantNumber.get(arg->term());
            }
            model.addFunctionDefinition(f,args,res);
          }
        }else{
          // not sure this makes sense but...
          if(!lit->polarity()) negated=!negated;
          // Defining a predicate or proposition
          unsigned p = lit->functor();
          unsigned arity = env.signature->predicateArity(p);
          if(arity==0) model.addPropositionalDefinition(p,!negated);
          else{
            DArray<unsigned> args(arity);
            for(unsigned i=0;i<arity;i++){
              TermList* arg = lit->nthArgument(i);
              if(arg->isVar() || !domainConstants.contains(arg->term()))
                USER_ERROR("Expect term on left of definition to be grounded with domain constants");
              args[i] = domainConstantNumber.get(arg->term());
            }
            model.addPredicateDefinition(p,args,!negated);
          }
        }
}

};

} // namespace FMB
#endif
