/**
 * @file TheoryInstAndSimp.cpp
 * Implements class TheoryInstAndSimp.
 */

#if VZ3

#define DPRINT 0

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/Splitter.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TheoryFlattening.hpp"

#include "SAT/SATLiteral.hpp"
#include "SAT/SAT2FO.hpp"
#include "SAT/Z3Interfacing.hpp"

#include "TheoryInstAndSimp.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;
using namespace SAT;


void TheoryInstAndSimp::attach(SaturationAlgorithm* salg)
{
  CALL("Superposition::attach");

  GeneratingInferenceEngine::attach(salg);
  _splitter = salg->getSplitter();
}

/**
 * 
 **/
void TheoryInstAndSimp::selectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits)
{
  CALL("TheoryInstAndSimp::selectTheoryLiterals");

  static Shell::Options::TheoryInstSimpSelection selection = env.options->theoryInstAndSimpSelection();

  Stack<Literal*> weak;
  Set<unsigned> strong_vars;
  Set<unsigned> strong_symbols;

  Clause::Iterator it(*cl);
  while(it.hasNext()){
    Literal* lit = it.next();
    bool interpreted = theory->isInterpretedPredicate(lit);

    // two var equalities are correctly identified as interpreted and should be added
    // for the other equalities, we make sure they don't contain uninterpreted stuff (after flattenning)

    //TODO I do this kind of check all over the place but differently every time!
    if(interpreted && lit->isEquality() && !lit->isTwoVarEquality()) {  
      for(TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()){
        if(ts->isTerm() && !env.signature->getFunction(ts->term()->functor())->interpreted()){
          interpreted=false;
          break;
        }
      }
    }
    if(interpreted){    
      VariableIterator vit(lit); 
      bool pos_equality = lit->isEquality() && lit->polarity();
      // currently weak literals are postive equalities or ground literals
      bool is_weak = !vit.hasNext() || pos_equality;
      if(selection != Shell::Options::TheoryInstSimpSelection::ALL && is_weak){
        weak.push(lit);
      }
      else{
#if DPRINT
        cout << "select " << lit->toString() << endl;
#endif
        theoryLits.push(lit);
        while(vit.hasNext()){ strong_vars.insert(vit.next().var()); } 
        NonVariableIterator nit(lit);
        while(nit.hasNext()){ strong_symbols.insert(nit.next().term()->functor());}
      }
    } 
  }
  if(selection != Shell::Options::TheoryInstSimpSelection::OVERLAP){
    return;
  }

  Stack<Literal*>::Iterator wit(weak);
  while(wit.hasNext()){
    Literal* lit = wit.next();
    VariableIterator vit(lit);
    bool add = false;
    while(vit.hasNext() && !add){
      if(strong_vars.contains(vit.next().var())){
        add=true; 
      }
    }
    if(!add){
      NonVariableIterator nit(lit); 
      while(nit.hasNext() && !add){
        if(strong_symbols.contains(nit.next().term()->functor())){
          add=true;
        }
      }
    }
    if(add){
#if DPRINT
        cout << "select " << lit->toString() << endl;
#endif
        theoryLits.push(lit);
    }
  }

}

Term* getFreshConstant(unsigned index, unsigned srt)
{
  CALL("TheoryInstAndSimp::getFreshConstant");
  static Stack<Stack<Term*>*> constants;

  while(srt+1 > constants.length()){
    Stack<Term*>* stack = new Stack<Term*>;
    constants.push(stack);
  }
  Stack<Term*>* sortedConstants = constants[srt]; 
  while(index+1 > sortedConstants->length()){
    unsigned sym = env.signature->addFreshFunction(0,"$$inst");
    FunctionType* type = new FunctionType(srt);
    env.signature->getFunction(sym)->setType(type);
    Term* fresh = Term::createConstant(sym);
    sortedConstants->push(fresh);
  }
  return (*sortedConstants)[index];
}

VirtualIterator<Solution> TheoryInstAndSimp::getSolutions(Stack<Literal*>& theoryLiterals){
  CALL("TheoryInstAndSimp::getSolutions");

  // Currently we just get the single solution from Z3

  // We use a new SMT solver
  SAT2FO naming;
  Z3Interfacing solver(*env.options,naming);


  // Firstly, we need to consistently replace variables by constants (i.e. Skolemize)
  // Secondly, we take the complement of each literal and consider the conjunction
  // This subst is for the consistent replacement
  Substitution subst;

  Stack<Literal*>::Iterator it(theoryLiterals);
  Stack<unsigned> vars;
  while(it.hasNext()){
    // get the complementary of the literal
    Literal* lit = Literal::complementaryLiteral(it.next());
    // replace variables consistently by fresh constants 
    DHMap<unsigned,unsigned > srtMap;
    SortHelper::collectVariableSorts(lit,srtMap); 
    TermVarIterator vit(lit);
    unsigned used = 0;
    while(vit.hasNext()){
      unsigned var = vit.next();
      unsigned sort = srtMap.get(var);
      TermList fc;
      if(!subst.findBinding(var,fc)){
        Term* fc = getFreshConstant(used++,sort);
        subst.bind(var,fc);
        vars.push(var);
      }
    }
#if DPRINT
    //cout << "skolem " << lit->toString();
#endif

    lit = SubstHelper::apply(lit,subst);

#if DPRINT
    //cout << " to get " << lit->toString() << endl;
#endif

    // register the lit in naming in such a way that the solver will pick it up!
    SATLiteral slit = naming.toSAT(lit);

    // now add the SAT representation
    static SATLiteralStack satLits;
    satLits.reset();
    satLits.push(slit);
    SATClause* sc = SATClause::fromStack(satLits); 
    //clause->setInference(new FOConversionInference(cl));
    solver.addClause(sc);
  }

  // now we can call the solver
  SATSolver::Status status = solver.solve(UINT_MAX);

  if(status == SATSolver::UNSATISFIABLE){
    return pvi(getSingletonIterator(Solution(false)));
  }
  else if(status == SATSolver::SATISFIABLE){
    Solution sol = Solution(true);
    Stack<unsigned>::Iterator vit(vars);
    while(vit.hasNext()){
      unsigned v = vit.next();
      Term* t = subst.apply(v).term();
      ASS(t);
      //cout << v << ": " << t->toString() << endl;
      t = solver.evaluateInModel(t);
      // If we could evaluate the term in the model then bind it
      if(t){
        //cout << "evaluate to " << t->toString() << endl;
        sol.subst.bind(v,t);
      }
    }
#if DPRINT
    cout << "solution with " << sol.subst.toString() << endl;
#endif
    return pvi(getSingletonIterator(sol));
  }

  // SMT solving was incomplete
  return VirtualIterator<Solution>::getEmpty(); 

}


struct InstanceFn
{
  InstanceFn(Clause* cl,Stack<Literal*>& tl,Splitter* sp) : _cl(cl), _theoryLits(tl), _splitter(sp) {}
  
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(Solution sol)
  {
    CALL("TheoryInstAndSimp::InstanceFn::operator()");

    // We should be deleting cl (it's a theory-tautology), but we don't support that for now
    // ... but does sol.status account for unknown?
    if(!sol.status){
      return 0;
    }
    // If the solution is empty (for any reason) there is no point performing instantiation
    if(sol.subst.isEmpty()){
      return 0;
    }
#if DPRINT
    cout << "Instantiate " << _cl->toString() << endl;
    cout << "with " << sol.subst.toString() << endl;
#endif
    Inference* inf_inst = new Inference1(Inference::INSTANTIATION,_cl);
    Clause* inst = new(_cl->length()) Clause(_cl->length(),_cl->inputType(),inf_inst);

    Inference* inf_simp = new Inference1(Inference::INTERPRETED_SIMPLIFICATION,inst);
    unsigned newLen = _cl->length() - _theoryLits.size();
    Clause* res = new(newLen) Clause(newLen,_cl->inputType(),inf_simp);

#if VDEBUG
    unsigned skip = 0;
#endif
    unsigned j=0;
    for(unsigned i=0;i<_cl->length();i++){
      Literal* lit = (*_cl)[i];
      Literal* lit_inst = SubstHelper::apply(lit,sol.subst);
      (*inst)[i] = lit_inst;
      // we implicitly remove all theoryLits as the solution makes their combination false
      if(!_theoryLits.find(lit)){
        (*res)[j] = lit_inst; 
        j++;
      }
#if VDEBUG
      else{skip++;}
#endif
    }
    ASS_EQ(skip, _theoryLits.size());
    ASS_EQ(j,newLen);

    if(_splitter){
      _splitter->onNewClause(inst);
    }

    env.statistics->theoryInstSimp++;
    return res;
  }

private:
  Clause* _cl;
  Stack<Literal*>& _theoryLits;
  Splitter* _splitter;
};

ClauseIterator TheoryInstAndSimp::generateClauses(Clause* premise)
{
  CALL("TheoryInstAndSimp::generateClauses");

  if(premise->isTheoryDescendant()){ return ClauseIterator::getEmpty(); }

  static Stack<Literal*> selectedLiterals;
  selectedLiterals.reset();

  selectTheoryLiterals(premise,selectedLiterals);

  // if there are no eligable theory literals selected then there is nothing to do
  if(selectedLiterals.isEmpty()){
        return ClauseIterator::getEmpty();
  }

  // we have an eligable candidate
  env.statistics->theoryInstSimpCandidates++;

  // TODO use limits
  //Limits* limits = _salg->getLimits();

  // we will use flattening which is non-recursive and sharing
  static TheoryFlattening flattener(false,true);

  Clause* flattened = flattener.apply(premise,selectedLiterals);

  ASS(flattened);

  // ensure that splits are copied to flattened
  if(_splitter && flattened!=premise){
    _splitter->onNewClause(flattened);
  }

  static Stack<Literal*> theoryLiterals;
  theoryLiterals.reset();

  // Now go through the abstracted clause and select the things we send to SMT
  // Selection and abstraction could be done in a single step but we are reusing existing theory flattening
  selectTheoryLiterals(flattened,theoryLiterals);

  // At this point theoryLiterals should contain abstracted versions of what is in selectedLiterals
  // all of the namings will be ineligable as, by construction, they will contain uninterpreted things

#if DPRINT
  cout << "Generate instances of " << premise->toString() << endl;
  cout << "With flattened " << flattened->toString() << endl;
#endif
  if(theoryLiterals.isEmpty()){
     //cout << "None" << endl;
     return ClauseIterator::getEmpty();
  }

  auto it1 = getSolutions(theoryLiterals);

  auto it2 = getMappingIterator(it1,InstanceFn(flattened,theoryLiterals,_splitter));

  // filter out only non-zero results
  auto it3 = getFilteredIterator(it2, NonzeroFn());

  // measure time of the overall processing
  auto it4 = getTimeCountedIterator(it3,TC_THEORY_INST_SIMP);

  return pvi(it4);
}

}

#endif
