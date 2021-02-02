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
 */
/**
 * @file TheoryInstAndSimp.cpp
 * Implements class TheoryInstAndSimp.
 */

#if VZ3
#define DEBUG(...) // DBG(__VA_ARGS__)

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
#include "Kernel/NumTraits.hpp"
#include "Kernel/TermIterators.hpp"

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

  SimplifyingGeneratingInference::attach(salg);
  _splitter = salg->getSplitter();
}

bool TheoryInstAndSimp::calcIsSupportedSort(const unsigned sort)
{
  CALL("TheoryInstAndSimp::calcIsSupportedSort")
  switch (sort) {
  case Kernel::Sorts::SRT_INTEGER:
  case Kernel::Sorts::SRT_RATIONAL:
  case Kernel::Sorts::SRT_REAL:
    return true;
  }
  if (env.signature->isTermAlgebraSort(sort)) {
    return env.signature->getTermAlgebraOfSort(sort)
                        ->subSorts().iter()
                         .all([&](unsigned s){ return env.signature->isTermAlgebraSort(s) || calcIsSupportedSort(s); });
  } else {
    return false;
  }
}

bool TheoryInstAndSimp::isSupportedSort(const unsigned sort) 
{ return _supportedSorts.getOrInit(sort, [&](){ return calcIsSupportedSort(sort); }); }

/**
  Wraps around interpretePredicate to support interpreted equality
 */
bool TheoryInstAndSimp::isSupportedLiteral(Literal* lit) {
  //check equality spearately (X=Y needs special handling)
  if (lit->isEquality()) {
    return isSupportedSort(SortHelper::getEqualityArgumentSort(lit));
  }

  //check if predicate is interpreted
  if (! theory->isInterpretedPredicate(lit->functor())){
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

bool TheoryInstAndSimp::isSupportedFunction(Term* trm) {
  auto sym = env.signature->getFunction(trm->functor());
  return !(theory->isInterpretedConstant(trm) 
      || (theory->isInterpretedFunction(trm) && isSupportedFunction(theory->interpretFunction(trm)) )
      || (sym->termAlgebraCons() && isSupportedSort(sym->fnType()->result()))
      || (sym->termAlgebraDest() && isSupportedSort(sym->fnType()->arg(0)))
      );
}


bool TheoryInstAndSimp::isSupportedFunction(Theory::Interpretation itp) {
  switch (itp) {
    case Theory::ARRAY_BOOL_SELECT:
    case Theory::ARRAY_SELECT:
    case Theory::ARRAY_STORE:
      return false;
    default: return true;
  }
}



bool TheoryInstAndSimp::isPure(Literal* lit) {
  if (lit->isSpecial()) /* TODO: extend for let .. in / if then else */ {
#if DPRINT
    cout << "special lit " << lit -> toString() << endl;
#endif
    return false;
  }

  //check if the predicate is a theory predicate
  if (! isSupportedLiteral(lit) ) {
    return false;
  }
  //check all (proper) subterms
  SubtermIterator sti(lit);
  while( sti.hasNext() ) {
    TermList tl = sti.next();
    if ( tl.isEmpty() || tl.isVar() ){
      continue;
    }
    if ( tl.isTerm()   ) {
      Term* term = tl.term();

      //we can stop if we found an uninterpreted function / constant
      if (isSupportedFunction(term)){
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
 *   1. L is of the form X != s where X does not occur in s
 *   2. L is pure
 *   3. for all literals L' in C that X (different from L) either
 *      + L' is not pure
 *      + L' is trivial in C
 *
 * some observations:
 *   - consider X != Y + 1 | Y != X - 1 | p(X,Y): then {}, as well as {X != Y+1, Y != X-1} are sets of trivial literals
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
Stack<Literal*> TheoryInstAndSimp::selectTrivialLiterals(Clause* cl)
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
  
  return triv_candidates;
}


/** 
 * Selects the theory literals to be used for instantiation. These are all non-trivial pure theory literals.
 */
Stack<Literal*> TheoryInstAndSimp::selectTheoryLiterals(Clause* cl) {
  CALL("TheoryInstAndSimp::selectTheoryLiterals");
#if DPRINT
  cout << "selectTheoryLiterals in " << cl->toString() << endl;
#endif

  ASS_NEQ(_mode, Shell::Options::TheoryInstSimp::OFF);

  Stack<Literal*> trivial_lits = selectTrivialLiterals(cl);
  Stack<Literal*> out;

  Clause::Iterator cl_it(*cl);
  while (cl_it.hasNext()) {
    auto lit = cl_it.next();
    // TODO this is O(n^2) runtime
    if (isPure(lit) && !trivial_lits.find(lit))
      out.push(lit);
  }
  return out;
}


void TheoryInstAndSimp::filterUninterpretedPartialFunctionDeep(Stack<Literal*>& theoryLits, Stack<Literal*>& filteredLits) {
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
        if( theory->isPartiallyInterpretedFunction(t)
         && theory->partiallyDefinedFunctionUndefinedForArgs(t)
            ){
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


VirtualIterator<Solution> TheoryInstAndSimp::getSolutions(Stack<Literal*> const& theoryLiterals, Stack<Literal*> const& guards) {
  CALL("TheoryInstAndSimp::getSolutions");

  BYPASSING_ALLOCATOR;

  // Currently we just get the single solution from Z3


  // Firstly, we need to consistently replace variables by constants (i.e. Skolemize)
  // Secondly, we take the complement of each literal and consider the conjunction
  // This subst is for the consistent replacement
  Substitution skolemSubst;

  Stack<SATLiteral> skolemized;
  Stack<unsigned> vars;
  unsigned used = 0;
  auto allLits = iterTraits(getConcatenatedIterator(
          iterTraits(theoryLiterals.iterFifo()).map(Literal::complementaryLiteral),
          guards.iterFifo()
        ));
  for (auto lit : allLits) {
    // replace variables consistently by fresh constants
    DHMap<unsigned,unsigned> srtMap;
    SortHelper::collectVariableSorts(lit,srtMap);
    TermVarIterator vit(lit);
    while(vit.hasNext()){
      unsigned var = vit.next();
      unsigned sort = srtMap.get(var);
      TermList fc;
      if(!skolemSubst.findBinding(var,fc)){
        Term* fc = getFreshConstant(used++,sort);
        skolemSubst.bind(var,fc);
        vars.push(var);
      }
    }

    lit = SubstHelper::apply(lit,skolemSubst);

    try {
      skolemized.push(_naming.toSAT(lit));
    } catch(UninterpretedForZ3Exception){
      return VirtualIterator<Solution>::getEmpty();
    }
  }

  // now we can call the solver
  SATSolver::Status status = _solver->solveWithAssumptions(skolemized);

  if(status == SATSolver::UNSATISFIABLE) {
    DEBUG("unsat")
    return pvi(getSingletonIterator(Solution(false)));

  } else if(status == SATSolver::SATISFIABLE){
    DEBUG("found model: ", _solver->getModel())
    auto buildSubstitution = [](Stack<unsigned> const& vars, Substitution& skolemSubst, Z3Interfacing& z3)  -> Option<Solution>
    {
      auto sol = Solution(true);
      auto vit = vars.iterFifo();
      while(vit.hasNext()){
        unsigned v = vit.next();
        Term* t = skolemSubst.apply(v).term();
        ASS(t);
        t = z3.evaluateInModel(t);
        // If we could evaluate the term in the model then bind it
        if(t){
          sol.subst.bind(v,t);
        } else {
          // Failed to obtain a value; could be an algebraic number or some other currently unhandled beast...
          env.statistics->theoryInstSimpLostSolution++;
          return Option<Solution>();
        }
      }
      return Option<Solution>(std::move(sol));
    };
    auto subst = buildSubstitution(vars, skolemSubst, *_solver);
    if (subst.isSome()) {
      return pvi(getSingletonIterator(std::move(subst).unwrap()));
    } else {
      DEBUG("could not build substituion from model.")
    }
  } else {
    // SMT solving was incomplete
    DEBUG("no solution.")
  }
  return VirtualIterator<Solution>::getEmpty();
}

Clause* instantiate(Clause* original, Substitution& subst, Stack<Literal*> const& theoryLits, Splitter* splitter)
{
  Clause* inst = new(original->length()) Clause(original->length(),GeneratingInference1(InferenceRule::INSTANTIATION,original));
  unsigned newLen = original->length() - theoryLits.size();
  Clause* res = new(newLen) Clause(newLen,SimplifyingInference1(InferenceRule::INTERPRETED_SIMPLIFICATION,inst));

  unsigned j=0;
  for(unsigned i=0;i<original->length();i++){
    Literal* lit = (*original)[i];
    Literal* lit_inst = SubstHelper::apply(lit,subst);
    (*inst)[i] = lit_inst;
    // we implicitly remove all theoryLits as the solution makes their combination false
    if(!theoryLits.find(lit)){
      (*res)[j] = lit_inst;
      j++;
    }
  }
  ASS_EQ(j,newLen);
  if(splitter){
    splitter->onNewClause(inst);
  }
  return res;
}


struct InstanceFn
{
  Clause* operator()(Solution sol, Clause* original, 
      Stack<Literal*> const& theoryLits, 
      Stack<Literal*> const& guards, 
      Splitter* splitter,
      TheoryInstAndSimp* parent, 
      bool& redundant
    )
  {
    CALL("TheoryInstAndSimp::InstanceFn::operator()");

    // We delete cl as it's a theory-tautology
    if(!sol.sat) {
      // now we run SMT solver again without guarding
      if(guards.isEmpty()){
        redundant = true;
      } else {
        auto solutions = parent->getSolutions(theoryLits, /* no guards */ Stack<Literal*>());
        // we have an unsat solution without guards
        redundant = solutions.hasNext() && !solutions.next().sat;
      }

      if (redundant) {
        env.statistics->theoryInstSimpTautologies++;
      }

      DEBUG("tautology")
      return nullptr;
    }
    // If the solution is empty (for any reason) there is no point performing instantiation
    if(sol.subst.isEmpty()){
      env.statistics->theoryInstSimpEmptySubstitution++;
    }
    auto res = instantiate(original, sol.subst, theoryLits, splitter);
    env.statistics->theoryInstSimp++;
    return res;
  }
};

Stack<Literal*> computeGuards(Stack<Literal*> const& lits) 
{
  CALL("computeGuards");

  /* finds the constructor for a given distructor */
  auto findConstructor = [](TermAlgebra* ta, unsigned destructor, bool predicate) -> TermAlgebraConstructor* 
  {
    // TODO get rid of this wasteful search for the right constructor
    for (auto ctor : ta->iterCons()) {
      for (unsigned i = 0; i < ctor->arity(); i++) {
        auto p = ctor->argSort(i) == Sorts::SRT_BOOL;
        auto d = ctor->destructorFunctor(i);
        if(destructor == d && predicate == p) 
          return ctor;
      }
    }
    ASSERTION_VIOLATION
  };

  auto destructorGuard = [&findConstructor](Term* destr, unsigned sort, bool predicate) -> Literal*
  {
      auto ctor = findConstructor(env.signature->getTermAlgebraOfSort(sort), destr->functor(), predicate);
      auto discr = ctor->createDiscriminator();
      // asserts e.g. isCons(l) for a term that contains the subterm head(l) for lists
      return Literal::create1(discr, /* polarity */ true, *destr->nthArgument(0));
  };


  Stack<Literal*> out;
  for (auto lit : lits) {

    /* guards for predicates */
    auto predSym = env.signature->getPredicate(lit->functor());
    if (predSym->termAlgebraDest()) {
      out.push(destructorGuard(lit, predSym->predType()->arg(0), /* predicate */ true));
    }

    /* guards for subterms */
    SubtermIterator it(lit);
    for (auto t = it.next(); it.hasNext(); t = it.next()) {
      ASS_REP(t.isVar() || !t.term()->isLiteral(), t);
      if (t.isTerm()) {
        auto term = t.term();
        auto sym = env.signature->getFunction(t.term()->functor());
        auto fun = term->functor();
        if (theory->isInterpretedNumber(term)) {
          /* no guard */
        } else if (theory->isInterpretedFunction(fun) || theory->isInterpretedConstant(fun)) {

          switch (theory->interpretFunction(fun)) {
            case Theory::REAL_QUOTIENT:
            case Theory::REAL_REMAINDER_E:
            case Theory::REAL_QUOTIENT_F:
            case Theory::REAL_QUOTIENT_T:
            case Theory::REAL_REMAINDER_T:
            case Theory::REAL_REMAINDER_F:
              out.push(Literal::createEquality(false, RealTraits::zero(), *term->nthArgument(1), RealTraits::sort));
              break;

            case Theory::RAT_QUOTIENT:
            case Theory::RAT_QUOTIENT_T:
            case Theory::RAT_REMAINDER_T:
            case Theory::RAT_QUOTIENT_F:
            case Theory::RAT_REMAINDER_F:
            case Theory::RAT_REMAINDER_E:
              out.push(Literal::createEquality(false, RatTraits::zero(), *term->nthArgument(1), RatTraits::sort));
              break;

            case Theory::INT_QUOTIENT_F:
            case Theory::INT_REMAINDER_F:
            case Theory::INT_QUOTIENT_E: 
            case Theory::INT_QUOTIENT_T:
            case Theory::INT_REMAINDER_T:
            case Theory::INT_REMAINDER_E:
              out.push(Literal::createEquality(false, IntTraits::zero(), *term->nthArgument(1), IntTraits::sort));
              break;

            default:; /* no guard */
          }
        } else if (sym->termAlgebraDest()) { 
          out.push(destructorGuard(term, sym->fnType()->arg(0), /* predicate */ false));
        }
      }
    }
  }
  return out;
}

bool isStrong(Literal* lit) 
{ return ( lit->isEquality() && lit->isNegative())
      || (!lit->isEquality() && theory->isInterpretedPredicate(lit->functor())); }

SimplifyingGeneratingInference::ClauseGenerationResult TheoryInstAndSimp::generateSimplify(Clause* premise)
{
  CALL("TheoryInstAndSimp::generateSimplify");

  auto empty = ClauseGenerationResult {
    .clauses          = ClauseIterator::getEmpty(),
    .premiseRedundant = false,
  };

  if(premise->isPureTheoryDescendant()){ 
    return empty;
  }


  Stack<Literal*> selectedLiterals = selectTheoryLiterals(premise);
  if (_mode == Options::TheoryInstSimp::STRONG) {
    selectedLiterals = iterTraits(selectedLiterals.iterFifo())
                          .filter(isStrong)
                          .collect<Stack>();
  }

  // if there are no eligable theory literals selected then there is nothing to do
  if(selectedLiterals.isEmpty()){
    return empty;
  }

  // we have an eligable candidate
  env.statistics->theoryInstSimpCandidates++;

  auto guards = computeGuards(selectedLiterals);

  DEBUG("input:             ", *premise);
  DEBUG("selected literals: ", iterTraits(selectedLiterals.iterFifo())
                                 .map([](Literal* l) -> vstring { return l->toString(); })
                                 .collect<Stack>())
  DEBUG("guards:            ", iterTraits(guards.iterFifo())
                                 .map([](Literal* l) -> vstring { return l->toString(); })
                                 .collect<Stack>())
  TimeCounter t(TC_THEORY_INST_SIMP);

  bool premiseRedundant = false;

  auto it1 = iterTraits(getSolutions(selectedLiterals, guards))
    .map([&](Solution s)  { 
        DEBUG("found solution: ", s); 
        return InstanceFn{}(s, premise, selectedLiterals, guards, _splitter, this, premiseRedundant);
    })
    .filter([](Clause* cl) { return cl != nullptr; });

  auto it2 = getTimeCountedIterator(it1,TC_THEORY_INST_SIMP);

  // we need to strictily evaluate the iterator to 
  auto clauses =  getPersistentIterator(it2);

  if (premiseRedundant && _thiTautologyDeletion) {
    return ClauseGenerationResult {
      .clauses          = ClauseIterator::getEmpty(),
      .premiseRedundant = true,
    };
  } else {
    return ClauseGenerationResult {
      .clauses          = clauses,
      .premiseRedundant = false,
    };
  }
}

std::ostream& operator<<(std::ostream& out, Solution const& self) 
{ return out << "Solution(" << (self.sat ? "sat" : "unsat") << ", " << self.subst << ")"; }

TheoryInstAndSimp::~TheoryInstAndSimp()
{
  CALL("~TheoryInstAndSimp")
  BYPASSING_ALLOCATOR
  delete _solver;
}

}

#endif
