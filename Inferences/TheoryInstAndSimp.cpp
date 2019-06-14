
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

#define DPRINT 1

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
#include "Kernel/Sorts.hpp"
#include "Kernel/Theory.hpp"

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

bool TheoryInstAndSimp::isSupportedSort(const unsigned sort) {
  //TODO: extend for more sorts (arrays, datatypes)
  switch (sort) {
  case Kernel::Sorts::SRT_INTEGER:
  case Kernel::Sorts::SRT_RATIONAL:
  case Kernel::Sorts::SRT_REAL:
    return true;
  default:
    if(env.sorts->isOfStructuredSort(sort,Sorts::StructuredSort::ARRAY)){
      unsigned idx = env.sorts->getArraySort(sort)->getIndexSort();
      unsigned inner = env.sorts->getArraySort(sort)->getInnerSort();
      //at the moment, boolean arrays are excluded
      bool r = isSupportedSort(idx) && isSupportedSort(inner);
      return r;
    }
  }

  return false;
}

/**
  Wraps around interpretePredicate to support interpreted equality
 */
bool TheoryInstAndSimp::isSupportedLiteral(Literal* lit) {
  //check equality spearately (X=Y needs special handling)
  if (lit->isEquality()) {
    unsigned sort = SortHelper::getEqualityArgumentSort(lit);
    return isSupportedSort(sort);
  }

  //check if predicate is interpreted
  if (! theory->isInterpretedPredicate(lit)){
    return false;
  }

  //check if arguments of predicate are supported
  for (unsigned i=0; i<lit->arity(); i++) {
    unsigned sort = SortHelper::getArgSort(lit,i);
    if (! isSupportedSort(sort))
      return false;
  }

  return true;
}


bool TheoryInstAndSimp::isPure(Literal* lit) {
  if (lit->isSpecial()) /* TODO: extend for let .. in / if then else */ {
#if DPRINT
    cout << "special lit " << lit -> toString() << endl;
#endif
    return false;
  }

  //check if the predicate is a theory predicate
  Theory* theory = Theory::instance();
  if (! isSupportedLiteral(lit) ) {
    //    cout << "uninterpreted predicate symbol " << lit -> toString() << endl;
    return false;
  }
  //check all (proper) subterms
  SubtermIterator sti(lit);
  while( sti.hasNext() ) {
    TermList tl = sti.next();
    //cout << "looking at subterm " << tl.toString() << endl;
    if ( tl.isEmpty() || tl.isVar() ){
      continue;
    }
    if ( tl.isTerm()   ) {
      Term* term = tl.term();

      //we can stop if we found an uninterpreted function / constant
      if (! (theory->isInterpretedFunction(term)  ||
             theory->isInterpretedConstant(term) )){
        return false;
      }
      //check if return value of term is supported
      if (! isSupportedSort(SortHelper::getResultSort(term))){
        return false;
      }
      //check if arguments of term are supported. covers e.g. f(X) = 0 where
      // f could map uninterpreted sorts to integer. when iterating over X
      // itself, its sort cannot be checked.
      for (unsigned i=0; i<term->arity(); i++) {
        unsigned sort = SortHelper::getArgSort(term,i);
        if (! isSupportedSort(sort))
          return false;
      }

    }
  }

#if DPRINT
  cout << "found pure literal: " << lit->toString() << endl;
#endif
  return true;
}

bool TheoryInstAndSimp::isXeqTerm(const TermList* left, const TermList* right) {
  bool r = left->isVar() &&
    right->isTerm() &&
    !IntList::member(left->var(), right->term()->freeVariables());
  return r;
}

unsigned TheoryInstAndSimp::varOfXeqTerm(const Literal* lit,bool flip) {
  ASS(lit->isEquality());
  ASS(! lit->isPositive());
  //add assertion
  if (lit->isEquality()) {
    const TermList* left = lit->nthArgument(0);
    const TermList* right = lit->nthArgument(1);
    if (isXeqTerm(left,right)){ return left->var();}
    if (isXeqTerm(right,left)){ return right->var();}
    ASS(lit->isTwoVarEquality());
    if(flip){
      return left->var(); 
    }else{
      return right->var();
    }
  }
  ASSERTION_VIOLATION ;
  return -1; //TODO: do something proper to prevent compilation warnings
}

/** checks if variable v is contained in literal lit */
bool TheoryInstAndSimp::literalContainsVar(const Literal* lit, unsigned v) {
  SubtermIterator it(lit);
  while (it.hasNext()) {
    const TermList t = it.next();
    if ((t.isVar()) && (t.var() == v)){
      return true;
    }
  }
  return false;
}


/**
 * Scans through a clause C and selects the largest set T s.t. all literals in
 * T are trivial. A literal L is trivial in C if:
 *   1 L is of the form X != s where X does not occur in s
 *   2 L is pure
 *   3 for all literals L' in C that X (different from L) either
 *      + L' is not pure
 *      + L' is trivial in C
 * some observations:
 *   - consider X != Y + 1 | Y != X - 1 | p(X,Y)
 *     then {} as well as {X != Y+1, Y != X-1} are sets of trivial literals
 *   - we can partition the clause into pure and impure literals
 *   - trivial literals are always a subset of the pure literals
 *   - a literal that violates condition is pure and not trivial
 * the algorithm is as follows:
 *   - find the set of trivial candidates TC that fulfill conditions 1 and 2
 *   - define the set of certainly non-trivial pure literals NT as
 *     { X in C | X is pure, X not in TC}
 *   - move all X from TC to NT that do not fulfill criterion 3
 *     (by checking against all elements of NT)
 *   - repeat this step until no element was removed or TC is empty
 * the algorithm can be optimized by only checking the freshly removed elements
 **/
void TheoryInstAndSimp::selectTrivialLiterals(Clause* cl,
                                              Stack<Literal*>& trivialLits)
{
  CALL("TheoryInstAndSimp::selectTrivialLiterals");
#if DPRINT
  cout << "selecting trivial literals in " << cl->toString() << endl ;
#endif
  /* find trivial candidates of the form x != t (x not occurring in t) */
  Clause::Iterator it(*cl);
  /* invariants:
       triv_candidates \cup nontriv_pure \cup impure = cl
       triv_candidates \cap nontriv_pure = 0
       triv_candidates \cap impure = 0
       nontriv_pure \cap impure = 0 */
  Stack<Literal*> triv_candidates;
  Stack<Literal*> nontriv_pure;
  Stack<Literal*> impure;
  while( it.hasNext() ) {
    Literal* c = it.next();
    if (isPure(c)) {
      //a liteal X != s is possibly trivial
      if (c->isNegative()
          && c->isEquality()) {
#if DPRINT
        cout << "checking " << c->toString() << endl;
#endif
        const TermList* left = c->nthArgument(0);
        const TermList* right = c->nthArgument(1);
        /* distinguish between X = s where s not a variable, X = Y and X = X */
        if (TheoryInstAndSimp::isXeqTerm(left, right) ||
            TheoryInstAndSimp::isXeqTerm(right, left) ) {
          triv_candidates.push(c);
        } else {
          // X=Y case
          if( left->isVar()
              && right->isVar()) {
            if (left->var() != right->var()) {
              triv_candidates.push(c);
            } else {
              //this is required by the definition, but making X=X trivial would
              //make more sense
              nontriv_pure.push(c);
            }
          } else { //term = term case
            nontriv_pure.push(c);
          }
        }
      } else {
        //mark as nontrivial pure
#if DPRINT
        cout << "non trivial pure found " << c->toString() << endl;
#endif
        nontriv_pure.push(c);
      }
    } else { // !isPure(c)
      impure.push(c);
    }
  }

#if DPRINT
  cout << "Found " << triv_candidates.length() << " trivial candidates." << endl;
  cout << "Found " << nontriv_pure.length() << " nontrivial pure literals." << endl;
  cout << "Found " << impure.length() << " impure literals." << endl;
#endif
  /* remove all candidates where the variable occurs in other pure
     non-trivial lits  */
  Stack<Literal*> nt_pure_tocheck(nontriv_pure);
  Stack<Literal*> nt_new;

  while( ! (nt_pure_tocheck.isEmpty() || triv_candidates.isEmpty()) ) {
    //for each candidate X=s, check if any literal in nt_pure_tocheck contains X
    //if yes, put it onto the removal list

    Stack<Literal*>::Iterator cand_it(triv_candidates);
    while(cand_it.hasNext() ) {
      Literal* cand = cand_it.next();
      Stack<Literal*>::Iterator tocheck_it(nt_pure_tocheck);
      while (tocheck_it.hasNext()) {
        Literal* checklit = tocheck_it.next();
        if (literalContainsVar(checklit, varOfXeqTerm(cand))) {
          nt_new.push(cand);
        }
        if(cand->isTwoVarEquality() && literalContainsVar(checklit,varOfXeqTerm(cand,true))){
          nt_new.push(cand);
        }
      } // ! nt_pure_tocheck.hasNext()
    }   // ! cand_it.hasNext()
    //remove nt_new from candidates, replace tocheck by nt_new
    Stack<Literal*>::Iterator nt_new_it(nt_new);
    while(nt_new_it.hasNext()) {
      triv_candidates.remove(nt_new_it.next());
    }
    nt_pure_tocheck = nt_new;
  }

#if DPRINT
  cout << "Found " << triv_candidates.length() << " trivial literals." << endl;
#endif
  
  //copy triv_candidates to trivialLits
  trivialLits = triv_candidates;
}


void TheoryInstAndSimp::selectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits) {
  CALL("TheoryInstAndSimp::selectTheoryLiterals");
#if DPRINT
  cout << "selectTheoryLiterals in " << cl->toString() << endl;
#endif

  static Shell::Options::TheoryInstSimp selection = env.options->theoryInstAndSimp();
  ASS(selection!=Shell::Options::TheoryInstSimp::OFF);

  //  Stack<Literal*> pure_lits;
  Stack<Literal*> trivial_lits;
  selectTrivialLiterals(cl, trivial_lits);

  Clause::Iterator cl_it(*cl);
  while (cl_it.hasNext()) {
    auto lit = cl_it.next();
    if (isPure(lit) && !trivial_lits.find(lit))
      theoryLits.push(lit);
  }
  
}


// literals containing top-level terms that are partial functions with 0 on the right should never be selected
// we only focus on top-level terms as otherwise the literal can be selected and have such terms abstracted out (abstraction treats
// these terms as uninterpreted) and then in the abstracted version we want them to not be selected!
  void TheoryInstAndSimp::filterDivisionByZero(Stack<Literal*>& theoryLits, Stack<Literal*>& filteredLits) {
  Stack<Literal*>::BottomFirstIterator it(theoryLits);
  while(it.hasNext()) {
    Literal* lit = it.next();
    bool keep_lit = true;
    for(TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()){
#if DPRINT
          cout << "div zero filtering checking: " << lit->toString() << endl;
#endif
      
      if(ts->isTerm()){
        Term* t = ts->term();
        if(theory->isInterpretedPartialFunction(t->functor()) &&
           theory->isZero(*(t->nthArgument(1)))){
          // treat this literal as uninterpreted
          keep_lit = false;
#if DPRINT
          cout << "division by zero removed: " << lit->toString() << endl;
#endif
        }
      }
    }

    if (keep_lit) {
      filteredLits.push(lit);
    }
  }
}

void TheoryInstAndSimp::filterDivisionByZeroDeep(Stack<Literal*>& theoryLits, Stack<Literal*>& filteredLits) {
#if DPRINT
  cout << "div zero filtering checking!" << endl;
#endif
  Stack<Literal*>::BottomFirstIterator it(theoryLits);
  while(it.hasNext()) {
    Literal* lit = it.next();
#if DPRINT
    cout << "div zero filtering checking: " << lit->toString() << endl;
#endif
    bool keep_lit = true;
    SubtermIterator sit(lit);
    while(sit.hasNext() && keep_lit){
      auto ts = sit.next();
      if(ts.isTerm()){
        Term* t = ts.term();
        if(theory->isInterpretedPartialFunction(t->functor()) &&
           theory->isZero(*(t->nthArgument(1)))){
          // treat this literal as uninterpreted
          keep_lit = false;
#if DPRINT
          cout << "division by zero removed: " << lit->toString() << endl;
#endif
        }
      }
    }

    if (keep_lit) {
      filteredLits.push(lit);
    }
  }
}

void TheoryInstAndSimp::applyFilters(Stack<Literal*>& theoryLits, bool forZ3) {
  //TODO: too much copying, optimize
  if (forZ3) {
    Stack<Literal*> filteredLits;
    filterDivisionByZeroDeep(theoryLits, filteredLits);
    theoryLits=filteredLits; 
  }
}

/**
 * Scans through a clause and selects candidates for theory instantiation
 **/
void TheoryInstAndSimp::originalSelectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits,bool forZ3)
{
  CALL("TheoryInstAndSimp::originalSelectTheoryLiterals");
#if DPRINT
  cout << "originalSelectTheoryLiterals["<<forZ3<<"] in " << cl->toString() << endl;
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


//TODO: put into interface
/* Take a theory (sub)clause, their skolemization grounding and a solution that makes the clause unsat.
   Return a new solution that is at least as general as the input solution.

   
 */
VirtualIterator<Solution>  minimizeSolution(Stack<Literal*>& theoryLiterals, bool guarded,
                                            Solution sol,  //Substitution subst,
                                            Stack<Literal*>& triangleSubst,
                                            unsigned maxVar
                                            //DHMap<unsigned,unsigned > srtMap
                                            ) {
  static SAT2FO naming;
  static  Z3Interfacing solver(*env.options,naming,true);
  solver.reset(); // the solver will reset naming

  Stack<Literal*>::Iterator it(theoryLiterals);
  Stack<unsigned> vars;
  unsigned used = 0;

  // abstract all terms in solution, create a stack of sat literals to
  // use for solving under assumptions. only the assumptions directly passed
  // to solveUnderAssumptions are added to the unsat core
  static TheoryFlattening flattener(true, false,false);
  Stack<Literal*> flattened;
  flattener.apply(triangleSubst, flattened,maxVar);
  Stack<Literal*> groundedFlattened;
  //  cerr << flattened.size() << endl;
  Substitution subst;
  Stack<Literal*>::Iterator stit(flattened);
  while(stit.hasNext()) {
    Literal* lit = stit.next();
#if DPRINT
    cerr << "subterm: " << lit->toString() << " of sort : " << env.sorts->sortName(SortHelper::getEqualityArgumentSort(lit));
#endif
    ASS(lit->isEquality());
    unsigned sort = SortHelper::getResultSort(lit->nthArgument(0)->term());
    unsigned v = lit->nthArgument(1)->var();
    Term* fc = getFreshConstant(used++,sort);
#if DPRINT
    cout << "     binding " << v << " to " << fc->toString() << endl;
#endif
    subst.bind(v,fc);
  }

  Stack<Literal*>::Iterator stit2(flattened);
  SATLiteralStack triangle_sateqs;
  while(stit2.hasNext()) {
    Literal* lit = Literal::complementaryLiteral(stit2.next())->apply(subst);
    groundedFlattened.push(lit);
#if DPRINT
    cerr << "adding model value: " << lit->toString() << endl;
#endif
    triangle_sateqs.push(naming.toSAT(lit));
  }

  //prepare theory clause and add it to the solver
  static SATLiteralStack satLits;
  satLits.reset();

  //create the literal with variables replaced by skolem constants
  while(it.hasNext()){
    // get the complementary of the literal
    Literal* lit = it.next();
    // apply substitution
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
    satLits.push(slit);
  }

  SATClause* sc = SATClause::fromStack(satLits);
  // guarded is normally true, apart from when we are checking a theory tautology
  try{
    solver.addClause(sc,guarded);
  }
  catch(UninterpretedForZ3Exception){
    return VirtualIterator<Solution>::getEmpty();
  }
  
  // TODO: add sk = term assertions for each element in the subst, label each assertion for consideration in unsat core

  // now we can call the solver
  SATSolver::Status status = solver.solveUnderAssumptions(triangle_sateqs, UINT_MAX, false);
  // check result is unsat and extract unsat core
  switch(status) {
  case SATSolver::Status::UNSATISFIABLE: {
#if DPRINT
    cerr << "SMT solver reports unsat when minimizing model!" << endl;
#endif
    SATLiteralStack unsat_core = solver.failedAssumptions();
#if DPRINT
    cerr << "unsat core size:" << unsat_core.size() << endl;
    for (SATLiteralStack::Iterator it(unsat_core); it.hasNext(); ) {
      cerr << "unsat core clause:" << it.next().toString() << endl;
    }
#endif
    //TODO: make implementation more efficient, intermediate substitutions are created
    // only keep variables in subst that appear in unsat core
    //  flattened terms are ordered by variable occurrence in subterms. we need to start with the last one
    Stack<Literal*>::BottomFirstIterator subterms(flattened);
    // the order in triangle_sateqs is the reverse of flattened, so we need to start with the first one here
    SATLiteralStack::Iterator substlits(triangle_sateqs);
    // keep a list of variables introduced by flattening. they must be removed from the solution
    Stack<unsigned> bindings_from_flattening;
    //the substitution that we will return in the solution
    Solution minsol(true);
#if DPRINT
    cerr << "filtering subst by unsat core:" << endl;
#endif
    while( substlits.hasNext() ) {
        ASS( subterms.hasNext() );
        SATLiteral sl = substlits.next();
        Literal* lit = subterms.next();
        if (unsat_core.find(sl)) {
#if DPRINT
          cerr << "taking subst lit: " << lit->toString() << endl;
#endif
          TermList t(lit->nthArgument(0)->term()->apply(minsol.subst));
          unsigned v = lit->nthArgument(1)->var();
          Substitution addsub;
          addsub.bind(v,t);
#if DPRINT
          //  cerr << "composing with " << TermList(v,false) << " -> " << t.toString() << endl;
          //  cerr << "composing with " << addsub.toString() << endl;
#endif
          minsol.subst.compose(addsub);

          if (v>maxVar) {
            bindings_from_flattening.push(v);
          }
        } else {
#if DPRINT
          cerr << "skipping subst lit: " << lit->toString() << endl;
#endif
        }
      }

      // removed flattening variables from minsol.sub
      for (Stack<unsigned>::Iterator it(bindings_from_flattening);
           it.hasNext();
           ) {
        unsigned v = it.next();
#if DPRINT
        cerr << "unbinding:" << v << endl;
#endif
        minsol.subst.unbind(v);
      }

#if DPRINT
      cerr << "minimized subst: " << minsol.subst.toString() << endl;
#endif      
      return pvi(getSingletonIterator(minsol));
    }
    break;
  case SATSolver::Status::UNKNOWN:
    cerr << "SMT solver reports unknown when minimizing model!" << endl;
#if VDEBUG
    cerr << "Sticking with" << sol.subst.toString() << endl;
#endif
    break;
  case SATSolver::Status::SATISFIABLE:
    cerr << "Input problem for instantiation minimization is always unsat, but solver reports sat!" << endl;
    ASS(false);
    break;
  }
  // return input solution when we couldnt construct a smaller one
  return pvi(getSingletonIterator(sol));

}


VirtualIterator<Solution> TheoryInstAndSimp::getSolutions(Stack<Literal*>& theoryLiterals, unsigned maxVar, bool guarded){
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
    Stack<Literal*> substTriangleForm;
    while(vit.hasNext()){
      unsigned v = vit.next();
      Term* t = subst.apply(v).term();
      ASS(t);
      //cout << v << ": " << t->toString() << endl;
      t = solver.evaluateInModel(t);
      // If we could evaluate the term in the model then bind it
      if(t){
        TermList tl_v(v,false);
        TermList tl_t(t);
        Literal* eq = Literal::createEquality(false, tl_v, tl_t, SortHelper::getResultSort(t));
#if DPRINT
        cerr << "assigning: " << eq->toString() << endl;
#endif
        substTriangleForm.push(eq);
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
    cout << "for literals: ";
    bool start = true;
    for (Stack<Literal*>::Iterator tlit(theoryLiterals); tlit.hasNext(); ) {
      if (start) { start = false; } else { cout << " | "; }
      cout << tlit.next()->toString();
    }
    cout << endl;
#endif
    // try to minimize the solution
    if (env.options->generalizeTheoryInstance()) {
      VirtualIterator<Solution> minsol = minimizeSolution(theoryLiterals, guarded, sol, substTriangleForm,maxVar);
      return minsol;
    }
    
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
  InstanceFn(Clause* premise,Clause* cl, Stack<Literal*>& tl,Splitter* splitter,
             SaturationAlgorithm* salg, TheoryInstAndSimp* parent,bool& red) :
         _premise(premise),  _cl(cl), _theoryLits(tl), _splitter(splitter),
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
        auto solutions = _parent->getSolutions(_theoryLits,_premise->maxVar(),false);
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
    cout << "theoryLits are" << endl;
    Stack<Literal*>::Iterator tit(_theoryLits);
    while(tit.hasNext()){ cout << "\t" << tit.next()->toString() << endl;}
#endif
    Clause* inst = new(_cl->length()) Clause(_cl->length(),GeneratingInference1(InferenceRule::INSTANTIATION,_cl));
    unsigned newLen = _cl->length() - _theoryLits.size();
    Clause* res = new(newLen) Clause(newLen,SimplifyingInference1(InferenceRule::INTERPRETED_SIMPLIFICATION,inst));

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
      else{skip++;}//cout << "skip " << lit->toString() << endl;}
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

  if(premise->isPureTheoryDescendant()){ return ClauseIterator::getEmpty(); }

  static Options::TheoryInstSimp thi = env.options->theoryInstAndSimp();

  static Stack<Literal*> selectedLiterals;
  selectedLiterals.reset();

  if(thi == Options::TheoryInstSimp::NEW){
    selectTheoryLiterals(premise,selectedLiterals);
    applyFilters(selectedLiterals,true);
  }
  else{
    originalSelectTheoryLiterals(premise,selectedLiterals,false);
  }

  // if there are no eligable theory literals selected then there is nothing to do
  if(selectedLiterals.isEmpty()){
        return ClauseIterator::getEmpty();
  }

  // we have an eligable candidate
  env.statistics->theoryInstSimpCandidates++;

  // TODO use limits

  Clause* flattened = premise;
  if(thi != Options::TheoryInstSimp::NEW){
    // we will use flattening which is non-recursive and sharing
    static TheoryFlattening flattener((thi==Options::TheoryInstSimp::FULL),true,true);

    flattened = flattener.apply(premise,selectedLiterals);

    ASS(flattened);

    // ensure that splits are copied to flattened
    if(_splitter && flattened!=premise){
      _splitter->onNewClause(flattened);
    }

    static Stack<Literal*> theoryLiterals;
    theoryLiterals.reset();

    // Now go through the abstracted clause and select the things we send to SMT
    // Selection and abstraction could be done in a single step but we are reusing existing theory flattening
    originalSelectTheoryLiterals(flattened,theoryLiterals,true);

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
    selectedLiterals.reset();
    selectedLiterals.loadFromIterator(Stack<Literal*>::Iterator(theoryLiterals));
  }

  {
    TimeCounter t(TC_THEORY_INST_SIMP);

    //auto it1 = getSolutions(theoryLiterals);
    auto it1 = getSolutions(selectedLiterals, premise->maxVar(), true);

    auto it2 = getMappingIterator(it1,
               InstanceFn(premise,flattened,selectedLiterals,_splitter,_salg,this,premiseRedundant));

    // filter out only non-zero results
    auto it3 = getFilteredIterator(it2, NonzeroFn());

    // measure time of the overall processing
    auto it4 = getTimeCountedIterator(it3,TC_THEORY_INST_SIMP);

    return pvi(it4);
  }
}

}

#endif
