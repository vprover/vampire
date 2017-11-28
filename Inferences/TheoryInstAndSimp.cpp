
/*
 * File TheoryInstAndSimp.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
void TheoryInstAndSimp::selectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits,bool forZ3)
{
  CALL("TheoryInstAndSimp::selectTheoryLiterals");
#if DPRINT
  cout << "selectTheoryLiterals["<<forZ3<<"] in " << cl->toString() << endl;
#endif

  static Shell::Options::TheoryInstSimp selection = env.options->theoryInstAndSimp();
  ASS(selection!=Shell::Options::TheoryInstSimp::OFF);

  Stack<Literal*> weak;
  Set<unsigned> strong_vars;
  Set<unsigned> strong_symbols;
  Array<Stack<Literal*>> var_to_lits(cl->varCnt());
  

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

    if(forZ3){
    // literals containing top-level terms that are partial functions with 0 on the right should never be selected
    // we only focus on top-level terms as otherwise the literal can be selected and have such terms abstracted out (abstraction treats
    // these terms as uninterpreted) and then in the abstracted version we want them to not be selected!
    for(TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()){
      if(ts->isTerm()){
        Term* t = ts->term();
        if(theory->isInterpretedPartialFunction(t->functor()) &&
           theory->isZero(*(t->nthArgument(1)))){
          // treat this literal as uninterpreted
          interpreted=false;
#if DPRINT
          cout << "forZ3 interpreted is false for " << lit->toString() << endl;
#endif
        }
      }
    }
    }

    if(interpreted){    
      VariableIterator vit(lit); 
      bool pos_equality = lit->isEquality() && lit->polarity();
      // currently weak literals are postive equalities or ground literals
      bool is_weak = !vit.hasNext() || pos_equality;
      if(selection != Shell::Options::TheoryInstSimp::ALL && 
         selection != Shell::Options::TheoryInstSimp::FULL && 
         is_weak){
        weak.push(lit);
      }
      else{
#if DPRINT
        cout << "select " << lit->toString() << endl;
#endif
        theoryLits.push(lit);
        while(vit.hasNext()){ 
          unsigned v = vit.next().var();
          strong_vars.insert(v); 
          var_to_lits[v].push(lit);
        }
        NonVariableIterator nit(lit);
        while(nit.hasNext()){ strong_symbols.insert(nit.next().term()->functor());}
      }
    } 
  }
  if(selection == Shell::Options::TheoryInstSimp::OVERLAP){

  Stack<Literal*>::Iterator wit(weak);
  while(wit.hasNext()){
    Literal* lit = wit.next();
#if DPRINT
	cout << "consider weak " << lit->toString() << endl;
#endif
    VariableIterator vit(lit);
    bool add = false;
    while(vit.hasNext() && !add){
      if(strong_vars.contains(vit.next().var())){
        add=true; 
#if DPRINT
	cout << "add weak as has strong var" << endl;
#endif
      }
    }
    if(!add){
      NonVariableIterator nit(lit); 
      while(nit.hasNext() && !add){
        if(strong_symbols.contains(nit.next().term()->functor())){
          add=true;
#if DPRINT
        cout << "add weak as has strong symbol" << endl;
#endif
        }
      }
    }
    if(add){
#if DPRINT
        cout << "select " << lit->toString() << endl;
#endif
        theoryLits.push(lit);
        VariableIterator vit(lit);
        while(vit.hasNext()){ var_to_lits[vit.next().var()].push(lit); } 
    }
  }
 
  }
  // now remove bad things
  // if this is the forZ3 pass then ensure that nothing is uninterpreted
  if(forZ3){
    Stack<Literal*>::Iterator tlit(theoryLits);
    Stack<Literal*> deselected;
    while(tlit.hasNext()){
      Literal* lit = tlit.next();
      NonVariableIterator nit(lit);
      bool deselect=false;
      while(nit.hasNext() && !deselect){
        Term* t = nit.next().term();
        deselect = !(theory->isInterpretedFunction(t->functor()) || theory->isInterpretedConstant(t->functor())); 
        if(deselect){
#if DPRINT
          cout << "deselect " << t->toString() << endl;
#endif
        }
      }
      if(deselect){ deselected.push(lit);}
    }
    Stack<Literal*>::Iterator dit(deselected);
    while(dit.hasNext()){ 
      Literal* lit = dit.next();
      theoryLits.remove(lit);
#if DPRINT
	cout << "deselect1 " << lit->toString() << endl;
#endif
    }
  }
  for(unsigned i=0;i<var_to_lits.size();i++){
    if(var_to_lits[i].size()==1){
      Literal * lit = var_to_lits[i][0]; 
      // is of the form X!=t where X only occurs in this literal (from theory literals)
      if(lit->isEquality() && !lit->polarity() &&
         ((lit->nthArgument(0)->isVar() && lit->nthArgument(0)->var()==i) || 
          (lit->nthArgument(1)->isVar() && lit->nthArgument(1)->var()==i))
         ){
#if DPRINT
        cout << "deselect2 " << lit->toString() << endl;
#endif
        theoryLits.remove(lit);
      }
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
    unsigned sym = env.signature->addFreshFunction(0,"$inst");
    OperatorType* type = OperatorType::getConstantsType(srt);
    env.signature->getFunction(sym)->setType(type);
    Term* fresh = Term::createConstant(sym);
    sortedConstants->push(fresh);
  }
  return (*sortedConstants)[index];
}

VirtualIterator<Solution> TheoryInstAndSimp::getSolutions(Stack<Literal*>& theoryLiterals, bool guarded){
  CALL("TheoryInstAndSimp::getSolutions");

  BYPASSING_ALLOCATOR;

  // Currently we just get the single solution from Z3

  // We use a new SMT solver
  // currently these are not needed outside of this function so we put them here
  static SAT2FO naming;
  static Z3Interfacing solver(*env.options,naming);
  solver.reset(); // the solver will reset naming


  // Firstly, we need to consistently replace variables by constants (i.e. Skolemize)
  // Secondly, we take the complement of each literal and consider the conjunction
  // This subst is for the consistent replacement
  Substitution subst;

  Stack<Literal*>::Iterator it(theoryLiterals);
  Stack<unsigned> vars;
  unsigned used = 0;
  while(it.hasNext()){
    // get the complementary of the literal
    Literal* lit = Literal::complementaryLiteral(it.next());
    // replace variables consistently by fresh constants 
    DHMap<unsigned,unsigned > srtMap;
    SortHelper::collectVariableSorts(lit,srtMap); 
    TermVarIterator vit(lit);
    while(vit.hasNext()){
      unsigned var = vit.next();
      unsigned sort = srtMap.get(var);
      TermList fc;
      if(!subst.findBinding(var,fc)){
        Term* fc = getFreshConstant(used++,sort);
#if DPRINT
    cout << "bind " << var << " to " << fc->toString() << endl;
#endif
        subst.bind(var,fc);
        vars.push(var);
      }
    }
#if DPRINT
    cout << "skolem " << lit->toString();
#endif

    lit = SubstHelper::apply(lit,subst);

#if DPRINT
    cout << " to get " << lit->toString() << endl;
#endif

    // register the lit in naming in such a way that the solver will pick it up!
    SATLiteral slit = naming.toSAT(lit);

    // now add the SAT representation
    static SATLiteralStack satLits;
    satLits.reset();
    satLits.push(slit);
    SATClause* sc = SATClause::fromStack(satLits); 
    //clause->setInference(new FOConversionInference(cl));
    // guarded is normally true, apart from when we are checking a theory tautology
    try{
      solver.addClause(sc,guarded);
    }
    catch(UninterpretedForZ3Exception){
      return VirtualIterator<Solution>::getEmpty();
    }
  }

  // now we can call the solver
  SATSolver::Status status = solver.solve(UINT_MAX);

  if(status == SATSolver::UNSATISFIABLE){
#if DPRINT
    cout << "z3 says unsat" << endl;
#endif
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
      } else {
        // Failed to obtain a value; could be an algebraic number or some other currently unhandled beast...
        env.statistics->theoryInstSimpLostSolution++;
        goto fail;
      }
    }
#if DPRINT
    cout << "solution with " << sol.subst.toString() << endl;
#endif
    return pvi(getSingletonIterator(sol));
  }

  fail:
#if DRPINT
    cout << "no solution" << endl;
#endif

  // SMT solving was incomplete
  return VirtualIterator<Solution>::getEmpty(); 

}


struct InstanceFn
{
  InstanceFn(Clause* premise, Clause* cl,Stack<Literal*>& tl,Splitter* splitter, 
             SaturationAlgorithm* salg, TheoryInstAndSimp* parent,bool& red) : 
         _premise(premise), _cl(cl), _theoryLits(tl), _splitter(splitter), 
         _salg(salg), _parent(parent), _red(red) {}
  
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(Solution sol)
  {
    CALL("TheoryInstAndSimp::InstanceFn::operator()");

    // We delete cl as it's a theory-tautology (note that if the answer was uknown no solution would be produced)
    if(!sol.status){
#if DPRINT
      cout << "Potential theory tautology" << endl;
#endif
      // if the theoryLits contain partial functions that need to be guarded then it may not
      // be a tautology, we would need to confirm this without the guards
      bool containsPartial = false;
      Stack<Literal*>::Iterator lit(_theoryLits);
      while(lit.hasNext()){
        NonVariableIterator tit(lit.next());
        while(tit.hasNext()){
          if(theory->isInterpretedPartialFunction(tit.next().term()->functor())){
            containsPartial=true;
            goto partial_check_end;
          }
        }
      }
partial_check_end:

      // now we run SMT solver again without guarding
      if(containsPartial){
        auto solutions = _parent->getSolutions(_theoryLits,false);
        // we have an unsat solution without guards
        if(solutions.hasNext() && !solutions.next().status){
          containsPartial=false;
        }
      }

      if(!containsPartial){
        env.statistics->theoryInstSimpTautologies++;
        // do this directly in salg
        //_salg->removeActiveOrPassiveClause(_premise);
        _red=true;
      }

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
#if DPRINT
    cout << "to get " << res->toString() << endl;
#endif
    return res;
  }

private:
  Clause* _premise;
  Clause* _cl;
  Stack<Literal*>& _theoryLits;
  Splitter* _splitter;
  SaturationAlgorithm* _salg;
  TheoryInstAndSimp* _parent;
  bool& _red;
};

ClauseIterator TheoryInstAndSimp::generateClauses(Clause* premise,bool& premiseRedundant)
{
  CALL("TheoryInstAndSimp::generateClauses");

  if(premise->isTheoryDescendant()){ return ClauseIterator::getEmpty(); }

  static Stack<Literal*> selectedLiterals;
  selectedLiterals.reset();

  selectTheoryLiterals(premise,selectedLiterals,false);

  // if there are no eligable theory literals selected then there is nothing to do
  if(selectedLiterals.isEmpty()){
        return ClauseIterator::getEmpty();
  }

  // we have an eligable candidate
  env.statistics->theoryInstSimpCandidates++;

  // TODO use limits
  //Limits* limits = _salg->getLimits();

  // we will use flattening which is non-recursive and sharing
  static Options::TheoryInstSimp thi = env.options->theoryInstAndSimp();
  static TheoryFlattening flattener((thi==Options::TheoryInstSimp::FULL),true);

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
  selectTheoryLiterals(flattened,theoryLiterals,true);

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

  auto it2 = getMappingIterator(it1,
               InstanceFn(premise,flattened,theoryLiterals,_splitter,_salg,this,premiseRedundant));

  // filter out only non-zero results
  auto it3 = getFilteredIterator(it2, NonzeroFn());

  // measure time of the overall processing
  auto it4 = getTimeCountedIterator(it3,TC_THEORY_INST_SIMP);

  return pvi(it4);
}

}

#endif
