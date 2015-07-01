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
#include "Lib/System.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/GeneralSplitting.hpp"

#include "ClauseFlattening.hpp"
#include "CombinationsIterator.hpp"
#include "DefinitionIntroduction.hpp"
#include "FiniteModelBuilder.hpp"

#define VTRACE_FMB 0

namespace FMB 
{

Array<Term*> FiniteModelBuilder::_modelConstants;
unsigned FiniteModelBuilder::created=0;
unsigned FiniteModelBuilder::fchecked=0;

FiniteModelBuilder::FiniteModelBuilder(Problem& prb, const Options& opt)
: MainLoop(prb, opt), _maxSatVar(0), _groundClauses(0), _clauses(0), _functionDefinitionClauses(0), _singleArityFunction(0), _isComplete(true), _maxModelSize(UINT_MAX)
{
  CALL("FiniteModelBuilder::FiniteModelBuilder");

  if(!opt.complete(prb)){
    _isComplete = false;
    return;
  }

  _incremental = opt.fmbIncremental();

  createSolver();
}

void FiniteModelBuilder::createSolver(){

  _maxSatVar = 0;
  _lookup.reset();
  _revLookup.reset();

  switch(_opt.satSolver()){
    case Options::SatSolver::VAMPIRE:
      _solver = new TWLSolver(_opt, true);
      break;
    case Options::SatSolver::LINGELING:
      _solver = new LingelingInterfacing(_opt, true);
      break;
    case Options::SatSolver::MINISAT:
      _solver = new MinisatInterfacing(_opt,true);
      break;
    default:
      ASSERTION_VIOLATION_REP(_opt.satSolver());
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

  if(!_isComplete) return;

  // Perform DefinitionIntroduction as we iterate
  // over the clauses of the problem
  DefinitionIntroduction cit = DefinitionIntroduction(_prb.clauseIterator());
  //ClauseIterator cit = _prb.clauseIterator();
  while(cit.hasNext()){
    Clause* c = cit.next();
#if VTRACE_FMB
    cout << "Flatten " << c->toString() << endl;
#endif
    c = ClauseFlattening::flatten(c);
#if VTRACE_FMB
    cout << "Flattened " << c->toString() << endl;
#endif
    ASS(c);

    if(isRefutation(c)){
      throw RefutationFoundException(c);
    }

    //TODO factor out
    if(c->varCnt()==0){
#if VTRACE_FMB
      //cout << "Add ground clause " << c->toString() << endl;
#endif
      _groundClauses = _groundClauses->cons(c);    
    }else{
#if VTRACE_FMB
      //cout << "Add non-ground clause " << c->toString() << endl;
#endif
      _clauses = _clauses->cons(c);

      unsigned posEqs = 0;
      for(unsigned i=0;i<c->length();i++){
        Literal* l = (*c)[i];
        if(l->isTwoVarEquality() && l->isPositive() && 
           (*l->nthArgument(0))!=(*l->nthArgument(1))
          ){ posEqs++; }
        else break;
      }
      if(posEqs == c->length() && c->varCnt() < _maxModelSize){
#if VTRACE_FMB
        cout << "based on " << c->toString() << " setting _maxModelSize to " << _maxModelSize << endl;
#endif
        _maxModelSize = c->varCnt();
      }      
    }
  }

  // Apply GeneralSplitting
  GeneralSplitting splitter;
  {
    TimeCounter tc(TC_FMB_SPLITTING);
    splitter.apply(_clauses);
  }

  // Normalise in place
  ClauseList::Iterator it(_clauses);
  while(it.hasNext()){
    Renaming n;
    Clause* c = it.next();

    //cout << "Normalize " << c->toString() <<endl;
    for(unsigned i=0;i<c->length();i++){
      Literal* l = (*c)[i];
      n.normalizeVariables(l);
      (*c)[i] = n.apply(l);
    }
#if VTRACE_FMB
    cout << "Normalized " << c->toString() << endl;
#endif

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

    static DArray<TermList> args(8);
    args.ensure(fun->arity());
    for(unsigned i=0;i<fun->arity();i++){
      args[i].makeVar(i+2);
    }
    TermList fargs = TermList(Term::create(f,fun->arity(),args.array()));
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
    _totalityFunctions.push(Term::create(f,fun->arity(),args.array()));

    //record constants
    if(fun->arity()==0){
      _constants.push(Term::createConstant(f));
    }
    //record first single arity function
    if(!_singleArityFunction && fun->arity()==1){
      _singleArityFunction = Term::create(f,1,args.array());
    }
  }

}

void FiniteModelBuilder::addGroundClauses()
{
  CALL("FiniteModelBuilder::addGroundClauses");

  // If we don't have any ground clauses don't do anything
  if(!_groundClauses) return;

  ClauseList::Iterator cit(_groundClauses);


addGroundLoop:
  while(cit.hasNext()){

      Clause* c = cit.next();
      ASS(c);

      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
#if VTRACE_FMB
      //cout << "Init: ";
#endif
      for(unsigned i=0;i<c->length();i++){
        Literal* lit = (*c)[i];
        // if tautology ignore clause
        if(EqHelper::isEqTautology(lit)){
#if VTRACE_FMB
          //cout << "Skipping tautology " << c->toString() << endl;
#endif
          goto addGroundLoop;
        }
        // if false, skip literal (okay because ground)
        if(lit->isEquality() && !lit->isPositive() &&
            (*lit->nthArgument(0))==(*lit->nthArgument(1))){
#if VTRACE_FMB
       //cout << "(" << lit->toString() << ") |";
#endif
          continue;
        }
#if VTRACE_FMB
        //cout << lit->toString() << " | ";
#endif
        SATLiteral slit = getSATLiteral(lit);
        satClauseLits.push(slit);
      }
#if VTRACE_FMB
      //cout << endl;
#endif
      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
  }
}

void FiniteModelBuilder::addNewInstances(unsigned size, bool incremental)
{
  CALL("FiniteModelBuilder::addNewInstances");

  ClauseList::Iterator cit(_clauses); 

  while(cit.hasNext()){
    Clause* c = cit.next();
    ASS(c);
#if VTRACE_FMB
    cout << "Instances of " << c->toString() << endl;
#endif

    unsigned fvars = c->varCnt();

    // If it's not incremental then create all
    CombinationsIterator it(fvars,size,!incremental);

instanceLoop:
    while(it.hasNext()){
      SubstCombination subst = it.next();

      static SATLiteralStack satClauseLits;
      satClauseLits.reset();

#if VTRACE_FMB
       cout << "Instance: ";
#endif
      // Ground and translate each literal into a SATLiteral
      for(unsigned i=0;i<c->length();i++){
        bool isTwoVar = ((*c)[i])->isTwoVarEquality();
        Literal* lit = SubstHelper::apply((*c)[i],subst);

        // check cases where literal is x=y
        // this will either skip the clause (tautology) or skip the literal (false)
        if(isTwoVar){
          bool equal = (*lit->nthArgument(0))==(*lit->nthArgument(1));
          if((lit->isPositive() && equal) || (!lit->isPositive() && !equal)){
#if VTRACE_FMB
              cout << "Skipped tautology" << endl;
#endif
              goto instanceLoop; 
          } 
          if((lit->isPositive() && !equal) || (!lit->isPositive() && equal)){
            //Skip literal
            continue;
          }
        }
#if VTRACE_FMB
        else{
          cout << lit->toString() << " | ";
        }
#endif
        SATLiteral slit = getSATLiteral(lit);
        satClauseLits.push(slit);
      }
#if VTRACE_FMB
      cout << endl;
#endif

      // if all literals have been deleted then we have an empty clause
      // that will be in this model and all larger models, therefore no model exists
      //TODO not sure this can actually happen, or if throwing this exception will work
      if(satClauseLits.isEmpty()){
        throw new RefutationFoundException(0);
      }

      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
    }
  }

}

void FiniteModelBuilder::addNewFunctionalDefs(unsigned size, bool incremental)
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

    // If it's not incremental consider all
    CombinationsIterator it(fvars,size,!incremental);

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

  // As we are _incremental we add the next one, which is for constant at position 'size'
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

unsigned FiniteModelBuilder::addNewTotalityDefs(unsigned size,bool incremental)
{
  CALL("FiniteModelBuilder::addNewTotalityDefs");

  unsigned domSizeVar = -1;
  SATLiteral domSizeLit;
  if(incremental){
    domSizeVar = getNextSATVar();
    domSizeLit = SATLiteral(domSizeVar,false);
  }

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
      if(incremental){
        satClauseLits.push(domSizeLit);
      }
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

      if(incremental){
        satClauseLits.push(domSizeLit);
      }

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
  _solver->ensureVarCount(++_maxSatVar);
  return _maxSatVar;
}

SATLiteral FiniteModelBuilder::getSATLiteral(Literal* lit)
{
  CALL("FiniteModelBuilder::getSATLiteral");
  bool polarity = lit->polarity();
  if(!polarity) lit = Literal::complementaryLiteral(lit);
  unsigned var;
  if(!_lookup.find(lit,var)){
    var = getNextSATVar();
#if VTRACE_FMB
    cout << "STORING " << var << " -> " << lit->toString() << endl;
#endif
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
#if VTRACE_FMB
  cout << "ADDING " << cl->toString() << endl;
#endif

  _clausesToBeAdded.push(cl);

}

MainLoopResult FiniteModelBuilder::runImpl()
{
  CALL("FiniteModelBuilder::runImpl");

  if(!_isComplete){
    // give up!
    return MainLoopResult(Statistics::UNKNOWN);
  }

  //TODO check about equality in EPR
  if(env.property->category()==Property::EPR){
    if(_constants.length() < _maxModelSize){
      _maxModelSize = _constants.length();
    }
  }

  unsigned modelSize = 1;
  int domSizeVar = -1;
  while(true){
#if VTRACE_FMB
    cout << "TRYING " << modelSize << endl;
#endif
    Timer::syncClock();
    if(env.timeLimitReached()){ return MainLoopResult(Statistics::TIME_LIMIT); }

    // if there was a previous domain variable, retract it
    // In non-_incremental mode domSizeVar never changes
    if(domSizeVar > -1){
      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
      satClauseLits.push(SATLiteral(domSizeVar,false));
      addSATClause(SATClause::fromStack(satClauseLits));

      // the solver can delete the previous totality clauses (minisat does)
      {
        TimeCounter tc(TC_FMB_SAT_SOLVING);
        _solver->simplify();
      }
    }

    {
    TimeCounter tc(TC_FMB_CONSTRAINT_CREATION);

    // add the new clauses to _clausesToBeAdded
#if VTRACE_FMB
    cout << "GROUND" << endl;
#endif
    if(!_incremental || modelSize == 1){
      addGroundClauses();
    }
#if VTRACE_FMB
    cout << "INSTANCES" << endl;
#endif
    addNewInstances(modelSize,_incremental);
#if VTRACE_FMB
    cout << "FUNC DEFS" << endl;
#endif
    addNewFunctionalDefs(modelSize,_incremental);
#if VTRACE_FMB
    cout << "SYM DEFS" << endl;
#endif
    if(!_incremental){
      for(unsigned s=1;s<modelSize;s++){
        addNewSymmetryAxioms(s);
      }
    }
    addNewSymmetryAxioms(modelSize);
#if VTRACE_FMB
    cout << "TOTAL DEFS" << endl;
#endif
    domSizeVar = addNewTotalityDefs(modelSize,_incremental);

    }

#if VTRACE_FMB
    cout << "SOLVING" << endl;
#endif
    //TODO consider adding clauses directly to SAT solver in new interface?
    // pass clauses and assumption to SAT Solver
    {
      TimeCounter tc(TC_FMB_SAT_SOLVING);
      _solver->addClausesIter(pvi(SATClauseStack::ConstIterator(_clausesToBeAdded)));
    }

    // only do this in _incremental mode
    if(_incremental){
      _solver->addAssumption(SATLiteral(domSizeVar,true));
    }

    SATSolver::Status satResult = SATSolver::UNKNOWN;
    {
      TimeCounter tc(TC_FMB_SAT_SOLVING);
      satResult = _solver->solve();
    }

    // if the clauses are satisfiable then we have found a finite model
    if(satResult == SATSolver::SATISFIABLE){
      onModelFound(modelSize);
      return MainLoopResult(Statistics::SATISFIABLE);
    }

    // In the unlikely event!
    if(modelSize == UINT_MAX){
      return MainLoopResult(Statistics::UNKNOWN);
    }

    if(modelSize >= _maxModelSize){

      if(env.options->mode()!=Options::Mode::SPIDER) { 
        if(env.property->category()==Property::EPR){
          cout << "Checked all constants of an EPR problem" << endl;
        }
        else{
          cout << "All further models will be UNSAT due to variable constraint" << endl;
        }
      }

      // create dummy empty clause as refutation
      Clause* empty = new(0) Clause(0,Unit::AXIOM,
         new Inference(Inference::MODEL_NOT_FOUND));
      return MainLoopResult(Statistics::REFUTATION,empty); 
    }

    if(_incremental){
      TimeCounter tc(TC_FMB_SAT_SOLVING);
      _solver->retractAllAssumptions();
    }

    if(!_incremental){
      // reset SAT Solver
      createSolver();

      // destroy the clauses
      SATClauseStack::Iterator it(_clausesToBeAdded);
      while (it.hasNext()) {
        it.next()->destroy();
      }
    } else {
      // clauses still live in the solver
    }
    // but the container needs to be empty for the next round in any case
    _clausesToBeAdded.reset();

    modelSize++;
  }


  return MainLoopResult(Statistics::UNKNOWN);
}

// Based on that found in InstGen
void FiniteModelBuilder::onModelFound(unsigned modelSize)
{
 // Don't do any output if proof is off
 if(_opt.proof()==Options::Proof::OFF){ 
   return; 
 }

 //we need to print this early because model generating can take some time
 if(UIHelper::cascMode) {
   env.beginOutput();
   env.out() << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
       << " for " << _opt.problemName() << endl << flush;
   env.endOutput();
   UIHelper::satisfiableStatusWasAlreadyOutput = true;
 }
 if(_opt.mode()==Options::Mode::SPIDER){
   reportSpiderStatus('-');
 }

  // Prevent timing out whilst the model is being printed
  Timer::setTimeLimitEnforcement(false);

 // Currently output this proof but look in InstGen/ModelPrinter
 // for how to print model properly

        cout << "Found model of size " << modelSize << endl;
        for(unsigned i=1;i<=_maxSatVar;i++){
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
}

}
