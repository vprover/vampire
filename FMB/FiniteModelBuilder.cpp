/**
 * @file FiniteModelBuilder.cpp
 * Implements class FiniteModelBuilder.
 */

#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Renaming.hpp"

#include "SAT/Preprocess.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/LingelingInterfacing.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/BufferedSolver.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/GeneralSplitting.hpp"

#include "ClauseFlattening.hpp"
#include "CombinationsIterator.hpp"
#include "FiniteModelBuilder.hpp"


namespace FMB 
{

FiniteModelBuilder::FiniteModelBuilder(Problem& prb, const Options& opt)
: MainLoop(prb, opt), _maxSatVar(1), _clauses(0), _functionDefinitionClauses(0)
{
  CALL("FiniteModelBuilder::FiniteModelBuilder");

  switch(opt.satSolver()){
    case Options::SatSolver::BUFFERED_VAMPIRE:
    case Options::SatSolver::VAMPIRE:
      _solver = new TWLSolver(opt, true);
      break;
    case Options::SatSolver::BUFFERED_LINGELING:
    case Options::SatSolver::LINGELING:
      _solver = new LingelingInterfacing(opt, true);
      break;
    case Options::SatSolver::BUFFERED_MINISAT:
    case Options::SatSolver::MINISAT:
      _solver = new MinisatInterfacing(opt,true);
      break;
    default:
      ASSERTION_VIOLATION_REP(opt.satSolver());
  }

}

void FiniteModelBuilder::init()
{
  CALL("FiniteModelBuilder::init");

  // Preprocess all clauses
  ClauseIterator cit = _prb.clauseIterator();
initLoop:
  while(cit.hasNext()){
    Clause* c = cit.next();
    c = ClauseFlattening::flatten(c);
    //cout << "Flattened " << c->toString() << endl;
    ASS(c);

    //TODO factr out
    if(c->varCnt()==0){
      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
      //cout << "Init: ";
      for(unsigned i=0;i<c->length();i++){
        Literal* lit = (*c)[i];
        // if tautology ignore clause
        if(EqHelper::isEqTautology(lit)){ goto initLoop; }
        // if false, skip literal (okay because ground)
        if(lit->isEquality() && !lit->isPositive() &&
            (*lit->nthArgument(0))==(*lit->nthArgument(1))){
          continue;
        }
        //cout << lit->toString() < " | ";
        SATLiteral slit = getSATLiteral(lit);
        satClauseLits.push(slit);
      }
      //cout << endl;
      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
    }else{
      _clauses = _clauses->cons(c);
    }
  }

  // Apply GeneralSplitting
  GeneralSplitting splitter;
  splitter.apply(_clauses);

  // Normalise in place
  ClauseList::Iterator it(_clauses);
  while(it.hasNext()){
    Renaming n;
    Clause* c = it.next();
    for(unsigned i=0;i<c->length();i++){
      Literal* l = (*c)[i];
      n.normalizeVariables(l);
      (*c)[i] = n.apply(l);
    }
  }

  // Create function definition clauses

  // For each function f of arity n we create the clause
  // f(x1,...,xn) != y | f(x1,...,xn) != z 
  // where y and z are X0 and X1 for ease of use later
  for(unsigned f = 0; f < env.signature->functions(); f++){

    Signature::Symbol* fun = env.signature->getFunction(f);
    ASS(fun);
    TermList y, z;
    y.makeVar(0); z.makeVar(1); 
    TermList args[fun->arity()];
    for(unsigned i=0;i<fun->arity();i++){
      args[i].makeVar(i+2);
    }
    TermList fargs = TermList(Term::create(f,fun->arity(),args));
    unsigned rSort = fun->fnType()->result(); 

    Clause* c = new(2) Clause(2,Unit::AXIOM, new Inference(Inference::FMB_FUNC_DEF));  
    Literal* l1 = Literal::createEquality(false,y,fargs,rSort);
    Literal* l2 = Literal::createEquality(false,z,fargs,rSort);
    (*c)[0] = l1;
    (*c)[1] = l2;
    
    //cout << "fdef " << c->toString() << endl;
    _functionDefinitionClauses = _functionDefinitionClauses->cons(c);

    //for use in totality definitions
    // now args must start from X0
    for(unsigned i=0;i<fun->arity();i++){
      args[i].makeVar(i);
    }
    _totalityFunctions.push(Term::create(f,fun->arity(),args));
  }

}

void FiniteModelBuilder::addNewInstances(unsigned size)
{
  CALL("FiniteModelBuilder::addNewInstances");

  ClauseList::Iterator cit(_clauses); 

  while(cit.hasNext()){
    Clause* c = cit.next();
    ASS(c);
    //cout << "Instances of " << c->toString() << endl;

    unsigned fvars = c->varCnt();

    CombinationsIterator it(fvars,size);

instanceLoop:
    while(it.hasNext()){
      SubstCombination subst = it.next();

      static SATLiteralStack satClauseLits;
      satClauseLits.reset();

       //cout << "Instance: ";
      // Ground and translate each literal into a SATLiteral
      for(unsigned i=0;i<c->length();i++){
        Literal* lit = SubstHelper::apply((*c)[i],subst);

        // if tautology ignore clause
        if(EqHelper::isEqTautology(lit)){ goto instanceLoop; }
        // if false, skip literal (okay because ground)
        if(lit->isEquality() && !lit->isPositive() &&
            (*lit->nthArgument(0))==(*lit->nthArgument(1))){
          continue;
        }
        //cout << lit->toString() << " | ";
        SATLiteral slit = getSATLiteral(lit);
        satClauseLits.push(slit);
      }
      //cout << endl;

      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
    }
  }

}

void FiniteModelBuilder::addNewFunctionalDefs(unsigned size)
{
  CALL("FiniteModelBuilder::addNewFunctionalDefs");

  // Similar to instances for function definitions
  // For each function f of arity n we have created the clause
  // f(x1,...,xn) != y | f(x1,...,xn) != z 
  // they should be instantiated with *new* substitutions where y!=z
  //
  // Importantly, y and z have been created as X0 and X1 so they can be identified
  //
  // TODO, consider sharing some code with addNewInstances

  ClauseList::Iterator cit(_functionDefinitionClauses);

  while(cit.hasNext()){
    Clause* c = cit.next();
    ASS(c);
    unsigned fvars = c->varCnt();
    ASS_G(fvars,0);

    CombinationsIterator it(fvars,size);

funDefLoop:
    while(it.hasNext()){
      SubstCombination subst = it.next();

      //Filter out substitutions that break the condition
      if(subst.apply(0) == subst.apply(1)){
        //cout << "Skipping ";subst.print();
        continue;
      }

      static SATLiteralStack satClauseLits;
      satClauseLits.reset();

      // Ground and translate each literal into a SATLiteral
      for(unsigned i=0;i<c->length();i++){
        Literal* lit = SubstHelper::apply((*c)[i],subst);
       if(EqHelper::isEqTautology(lit)){ goto funDefLoop; }
        // if false, skip literal (okay because ground)
        if(lit->isEquality() && !lit->isPositive() &&
            (*lit->nthArgument(0))==(*lit->nthArgument(1))){
          continue;
        }
        SATLiteral slit = getSATLiteral(lit);
        satClauseLits.push(slit);
      }

      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
    }
  }
  
}

unsigned FiniteModelBuilder::addNewTotalityDefs(unsigned size)
{
  CALL("FiniteModelBuilder::addNewTotalityDefs");

  unsigned domSizeVar = getNextSATVar();
  SATLiteral domSizeLit = SATLiteral(domSizeVar,false);

  Stack<Term*>::Iterator tit(_totalityFunctions);

  while(tit.hasNext()){
    Term* t = tit.next();
    ASS(t);
    //cout << "Totals for " << t->toString() << endl;

    unsigned rSort = SortHelper::getResultSort(t);
    unsigned fvars = t->arity();

    if(fvars==0){
      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
      satClauseLits.push(domSizeLit);
      for(unsigned i=0;i<size;i++){
        Term* c = SubstCombination::getConstant(i+1);
        Literal* lit = Literal::createEquality(true,TermList(t),TermList(c),rSort);
        SATLiteral slit = getSATLiteral(lit);
        satClauseLits.push(slit);
      }
      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl); 
      continue;
    }

    CombinationsIterator it(fvars,size,true); //true indicates we want ALL
    while(it.hasNext()){
      SubstCombination subst = it.next();
      //cout << "Using ";subst.print();

      Term* tsub = SubstHelper::apply(t,subst);

      static SATLiteralStack satClauseLits;
      satClauseLits.reset();

      satClauseLits.push(domSizeLit);

      // Ground and translate each literal into a SATLiteral
      for(unsigned i=0;i<size;i++){
        // constants are 1-based
        Term* c = SubstCombination::getConstant(i+1);
        Literal* lit = Literal::createEquality(true,TermList(tsub),TermList(c),rSort);
        SATLiteral slit = getSATLiteral(lit);
        satClauseLits.push(slit);
      }    

      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
    }
  }
  
  return domSizeVar;
}


unsigned FiniteModelBuilder::getNextSATVar()
{
  CALL("FiniteModelBuilder::getNextSATLiteral");
  // currently just get a positive fresh literal
  _solver->ensureVarCnt(_maxSatVar+1);
  return _maxSatVar++;
}

SATLiteral FiniteModelBuilder::getSATLiteral(Literal* lit)
{
  CALL("FiniteModelBuilder::getSATLiteral");
  bool polarity = lit->polarity();
  if(!polarity) lit = Literal::complementaryLiteral(lit);
  unsigned var;
  if(!_lookup.find(lit,var)){
    var = getNextSATVar();
    //cout << "STORING " << var << " -> " << lit->toString() << endl;
    _lookup.insert(lit,var);
    _revLookup.insert(var,lit);
  }
  return SATLiteral(var,polarity);
}

void FiniteModelBuilder::addSATClause(SATClause* cl)
{
  CALL("FiniteModelBuilder::addSATClause");
  cl = Preprocess::removeDuplicateLiterals(cl);
  if(!cl){ return; }

  //cout << "ADDING " << cl->toString() << endl;

  _clausesToBeAdded.push(cl);

}

MainLoopResult FiniteModelBuilder::runImpl()
{
  CALL("FiniteModelBuilder::runImpl");

  unsigned modelSize = 1;
  int domSizeVar = -1;
  while(true){
    cout << "TRYING " << modelSize << endl;
    Timer::syncClock();
    if(env.timeLimitReached()){ return MainLoopResult(Statistics::TIME_LIMIT); }

    // if there was a previous domain variable, retract it
    if(domSizeVar > -1){
      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
      satClauseLits.push(SATLiteral(domSizeVar,false));
      addSATClause(SATClause::fromStack(satClauseLits));
    }

    // add the new clauses to _clausesToBeAdded
    //cout << "INSTANCES" << endl;
    addNewInstances(modelSize);
    //cout << "FUNC DEFS" << endl;
    addNewFunctionalDefs(modelSize);
    //cout << "TOTAL DEFS" << endl;
    domSizeVar = addNewTotalityDefs(modelSize);

    // pass clauses and assumption to SAT Solver
    _solver->addClauses(pvi(SATClauseStack::ConstIterator(_clausesToBeAdded)));
    _clausesToBeAdded.reset();
    _solver->addAssumption(SATLiteral(domSizeVar,true));

    // if the clauses are satisfiable then we have found a finite model
    if(_solver->solve() == SATSolver::SATISFIABLE){

      cout << "Found model of size " << modelSize << endl;
      for(unsigned i=1;i<_maxSatVar;i++){
        Literal* lit;
        if(_revLookup.find(i,lit)){
          bool pol = _solver->trueInAssignment(SATLiteral(i,true)); 
          ASS(pol || !lit->isEquality() || lit->nthArgument(0)!=lit->nthArgument(1));
          if(!pol) lit = Literal::complementaryLiteral(lit);
          if(!lit->isEquality() || (pol && !EqHelper::isEqTautology(lit))){ 
            cout << lit->toString() << endl;
          }
        }
      }

      return MainLoopResult(Statistics::SATISFIABLE);
    }

    _solver->retractAllAssumptions();
    modelSize++;
  }


  return MainLoopResult(Statistics::UNKNOWN);
}


}
