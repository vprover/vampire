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
#include "Kernel/Substitution.hpp"

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
#include "DefinitionIntroduction.hpp"
#include "FiniteModelBuilder.hpp"


namespace FMB 
{

Array<Term*> FiniteModelBuilder::_modelConstants;
unsigned FiniteModelBuilder::created=0;
unsigned FiniteModelBuilder::fchecked=0;

FiniteModelBuilder::FiniteModelBuilder(Problem& prb, const Options& opt)
: MainLoop(prb, opt), _maxSatVar(1), _clauses(0), _functionDefinitionClauses(0), _singleArityFunction(0)
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

Term* FiniteModelBuilder::getConstant(unsigned constant)
{
  CALL("FiniteModelBuilder::getConstant");
      while(constant >= created){
        vstring name;
        bool found=false;

// This is the code that makes us reuse constants in the problem
// turned off for now as output is clearer without it
/*
        while(!found && fchecked<env.signature->functions()){
          fchecked++;
          Signature::Symbol* fun = env.signature->getFunction(fchecked); 
          if(fun->arity()==0){
            found=true;
            name=fun->name(); 
          }
        }
*/
        if(!found){
          name = "fmb_" + Lib::Int::toString(created);
        }
        _modelConstants[created] = Term::createConstant(name);
        created++;
      }
      return _modelConstants[constant];

}


void FiniteModelBuilder::init()
{
  CALL("FiniteModelBuilder::init");

  // Perform DefinitionIntroduction as we iterate
  // over the clauses of the problem
  DefinitionIntroduction cit = DefinitionIntroduction(_prb.clauseIterator());
initLoop:
  while(cit.hasNext()){
    Clause* c = cit.next();
    c = ClauseFlattening::flatten(c);
    //cout << "Flattened " << c->toString() << endl;
    ASS(c);

    if(isRefutation(c)){
      throw RefutationFoundException(c);
    }

    //TODO factor out
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

    //record constants
    if(fun->arity()==0){
      _constants.push(Term::createConstant(f));
    }
    //record first single arity function
    if(!_singleArityFunction && fun->arity()==1){
      _singleArityFunction = Term::create(f,1,args);
    }
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

void FiniteModelBuilder::addNewSymmetryAxioms(unsigned size)
{
  CALL("FiniteModelBuilder::addNewSymmetryAxioms");

  // If all constants have been used then start adding function symmetries
  if(_constants.size() <= size){
    if(!_singleArityFunction) return; //TODO create one by i.e. f(x) = g(x,x)
    if(_constants.size()==0) return;  //TODO create a fake constant

    // now add clause
    // f(c)=1 | f(c)=2 | f(c)=3 | ... | f(c)=size
    // where we take c to be size-k for k constants
    // TODO, consider if there is something better we can add

    int ci = (size-_constants.size());
    ASS(ci >= 0);
    Term* c = getConstant(ci+1);
    Substitution s;
    s.bind(0,c);
    Term* fc = SubstHelper::apply(_singleArityFunction,s);
    unsigned sort = SortHelper::getResultSort(fc);

    static SATLiteralStack satClauseLits;
    satClauseLits.reset();

    for(unsigned i=0;i<size;i++){
      Term* c2 = getConstant(i+1); 
      Literal* l = Literal::createEquality(true,TermList(fc),TermList(c2),sort);
      SATLiteral sl = getSATLiteral(l);
      satClauseLits.push(sl);
    }
    
    SATClause* satCl = SATClause::fromStack(satClauseLits);
    addSATClause(satCl);

    // do not add any constant symmetries
    return;
  }

  // First add restricted totality for constants (TODO remove totality for constants?)
  // i.e. for constant a1 add { a1=1 } and for a2 add { a2=1, a2=2 } and so on

  // As we are incremental we add the next one, which is for constant at position 'size'
  Term* c1 = _constants[size-1]; // size 1-based, index 0-based
  unsigned sort = SortHelper::getResultSort(c1);

  static SATLiteralStack satClauseLits;
  satClauseLits.reset(); 
  for(unsigned i=0;i<size;i++){
    Term* c2 = getConstant(i+1); 
    Literal* l = Literal::createEquality(true,TermList(c1),TermList(c2),sort);
    SATLiteral sl = getSATLiteral(l);
    satClauseLits.push(sl);
  }
  SATClause* satCl = SATClause::fromStack(satClauseLits);
  addSATClause(satCl);

  // Now new add canonicity clauses of the form
  // ai = d => a1=d | a2=d-1 | ... ai-1 =d-1
  // for i=size and d>1
  // i.e. if this constant is equal to d then there is a smaller one that is
  // only do this for i>1
  if(size > 1){
    for(unsigned d=1;d<size;d++){
      satClauseLits.reset();

      Term* cd = getConstant(d+1); 
      Term* cdm = getConstant(d); 

      Literal* l = Literal::createEquality(false,TermList(c1),TermList(cd),sort); 
      satClauseLits.push(getSATLiteral(l));

      for(unsigned i=0;i<size-1;i++){
        Term* ci = _constants[i]; 
        l = Literal::createEquality(true,TermList(ci),TermList(cdm),sort);
        satClauseLits.push(getSATLiteral(l));
      }

      addSATClause(SATClause::fromStack(satClauseLits));
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
        Term* c = getConstant(i+1);
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
        Term* c = getConstant(i+1);
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

  bool isEPR = env.property->category()==Property::EPR;

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
    //cout << "SYM DEFS" << endl;
    addNewSymmetryAxioms(modelSize);
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

    // If it's EPR and we've used all the constants and not found a model then there is no model
    if(isEPR && modelSize==_constants.length()){
      return MainLoopResult(Statistics::REFUTATION); //TODO is REFUTATION the right one?
    }

    _solver->retractAllAssumptions();
    modelSize++;
  }


  return MainLoopResult(Statistics::UNKNOWN);
}


}
