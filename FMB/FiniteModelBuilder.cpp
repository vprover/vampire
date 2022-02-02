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
 * @file FiniteModelBuilder.cpp
 * Implements class FiniteModelBuilder.
 *
 * NOTE: An important convention to remember is that when we have a DArray representing
 *       the signature or grounding of a function the lastt argument is the return
 *       so array[arity] is return and array[i] is the ith argument of the function
 */

#include <cmath>

#include "Kernel/Ordering.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "SAT/MinisatInterfacingNewSimp.hpp"
#include "SAT/BufferedSolver.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Random.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/ArrayMap.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/GeneralSplitting.hpp"

#include "DP/DecisionProcedure.hpp"
#include "DP/SimpleCongruenceClosure.hpp"

#include "FiniteModelMultiSorted.hpp"
#include "ClauseFlattening.hpp"
#include "SortInference.hpp"
#include "DefinitionIntroduction.hpp"
#include "FunctionRelationshipInference.hpp"
#include "CliqueFinder.hpp"
#include "Monotonicity.hpp"
#include "FiniteModelBuilder.hpp"

#define VTRACE_FMB 0

#define VTRACE_DOMAINS 0

#define LOG(X) // cout << #X <<  X << endl;

namespace FMB 
{

FiniteModelBuilder::FiniteModelBuilder(Problem& prb, const Options& opt)
: MainLoop(prb, opt), _sortedSignature(0), _groundClauses(0), _clauses(0),
                      _isAppropriate(true)

{
  CALL("FiniteModelBuilder::FiniteModelBuilder");

  Property& prop = *prb.getProperty();

  LOG(prop.hasInterpretedOperations());
  LOG(prop.hasProp(Property::PR_HAS_INTEGERS));
  LOG(prop.hasProp(Property::PR_HAS_REALS));
  LOG(prop.hasProp(Property::PR_HAS_RATS));
  LOG(prop.hasProp(Property::PR_HAS_DT_CONSTRUCTORS));
  LOG(prop.hasProp(Property::PR_HAS_CDT_CONSTRUCTORS));
  LOG(prop.knownInfiniteDomain());

  if (prop.hasInterpretedOperations()
      ||  prop.hasProp(Property::PR_HAS_INTEGERS)
      || prop.hasProp(Property::PR_HAS_REALS)
      || prop.hasProp(Property::PR_HAS_RATS)
      || prop.knownInfiniteDomain() || // recursive data type provably infinite --> don't bother model building
      env.property->hasInterpretedOperations()) {

      env.beginOutput();
      addCommentSignForSZS(env.out());
      env.out() << "WARNING: trying to run FMB on interpreted or otherwise provably infinite-domain problem!" << endl;
      env.endOutput();

     _isAppropriate = false;
     _dsaEnumerator = 0; // to ensure it is initialised
     return;
  }

  if (prb.hadIncompleteTransformation() ||
      opt.sineSelection() != Options::SineSelection::OFF) {
    _isAppropriate = false;
    _dsaEnumerator = 0; // to ensure it is initialised
    return;
  }

  // Record option values
  _startModelSize = opt.fmbStartSize();
  _symmetryRatio = opt.fmbSymmetryRatio();

  // Load any symbols removed during preprocessing (and their definitions)
  _deletedFunctions.loadFromMap(prb.getEliminatedFunctions());
  _deletedPredicates.loadFromMap(prb.getEliminatedPredicates());
  _partiallyDeletedPredicates.loadFromMap(prb.getPartiallyEliminatedPredicates());
  _trivialPredicates.loadFromMap(prb.trivialPredicates());

  switch(opt.fmbEnumerationStrategy()) {
    case Options::FMBEnumerationStrategy::SBMEAM:
      _dsaEnumerator = new HackyDSAE();
      _xmass = false;
      break;
#if VZ3
    case Options::FMBEnumerationStrategy::SMT:
      {
        BYPASSING_ALLOCATOR;

        _dsaEnumerator = new SmtBasedDSAE();
      }
      _xmass = false;
      break;
#endif
    case Options::FMBEnumerationStrategy::CONTOUR:
      _dsaEnumerator = 0;
      _xmass = true;
      _sizeWeightRatio = opt.fmbSizeWeightRatio();
      break;
    default:
      ASSERTION_VIOLATION;
  }
}

FiniteModelBuilder::~FiniteModelBuilder()
{
  CALL("FiniteModelBuilder::~FiniteModelBuilder");

  if(_dsaEnumerator){
    BYPASSING_ALLOCATOR;

    delete _dsaEnumerator;
  }
}

// Do all setting up required for finite model search 
// Returns false we if we failed to reset, this can happen if offsets overflow 2^32, possible for
// large signatures and large models. If this a frequent problem then we can go to longs.
bool FiniteModelBuilder::reset(){
  CALL("FiniteModelBuilder::reset");

  // Construct the offsets for symbols
  // Each symbol requires size^n) variables where n is the number of spaces for grounding
  // For function symbols we have n=arity+1 as we have the return value
  // For predicate symbols n=arity 


  // This has been refined after adding multiple sorts i.e. no general 'size'
  // We now need the current size of the sort of each position to compute the offsets

  static const unsigned VAR_MAX = MinisatInterfacingNewSimp::VAR_MAX;

  // Start from 1 as SAT solver variables are 1-based
  unsigned offsets=1;
  for(unsigned f=0; f<env.signature->functions();f++){
    if(del_f[f]) continue; 
    f_offsets[f]=offsets;
#if VTRACE_FMB
    cout << "offset for " << f << " is " << offsets << " (arity is " << env.signature->functionArity(f) << ") " << endl;
#endif

    DArray<unsigned> f_signature = _sortedSignature->functionSignatures[f];
    ASS(f_signature.size() == env.signature->functionArity(f)+1);

    unsigned add = _sortModelSizes[f_signature[0]]; 
    for(unsigned i=1;i<f_signature.size();i++){
      unsigned n_add = add * _sortModelSizes[f_signature[i]];
      if (n_add < add) { // additional overflow check - we multiply by positive integers!
        return false;
      }
      add = n_add;
    }

    // Check that we do not overflow
    if(VAR_MAX - add < offsets){
      return false;
    }
    offsets += add;
  }
  // Start from p=1 as we ignore equality
  for(unsigned p=1; p<env.signature->predicates();p++){
    if(del_p[p]) continue;
    p_offsets[p]=offsets;
#if VTRACE_FMB
    cout << "offset for " << p << " is " << offsets << " for " << env.signature->predicateName(p) << endl; 
 
#endif

    DArray<unsigned> p_signature = _sortedSignature->predicateSignatures[p];
    ASS(p_signature.size()==env.signature->predicateArity(p));
    unsigned add=1;
    for(unsigned i=0;i<p_signature.size();i++){
      unsigned n_add = add * _sortModelSizes[p_signature[i]];
      if (n_add < add) { // additional overflow check - we multiply by positive integers!
        return false;
      }
      add = n_add;
    }

    // Check for overflow
    if(VAR_MAX - add < offsets){
      return false;
    }
    offsets += add; 
  }

#if VTRACE_FMB
  cout << "Maximum offset is " << offsets << endl;
#endif

  if (_xmass) {
    marker_offsets.ensure(_distinctSortSizes.size());
    for (unsigned i = 0; i < _distinctSortSizes.size(); i++) {
      unsigned add = _distinctSortSizes[i];

      marker_offsets[i] = offsets;

      // Check for overflow
      if(VAR_MAX - add < offsets){
        return false;
      }

      offsets += add;
    }
  } else {
    unsigned add = _distinctSortSizes.size();

    totalityMarker_offset = offsets;

    // Check for overflow
    if(VAR_MAX - add < offsets){
      return false;
    }

    offsets += add;

    instancesMarker_offset = offsets;

    // Check for overflow
    if(VAR_MAX - add < offsets){
      return false;
    }

    offsets += add;
  }

  // Create a new SAT solver
  try{
    _solver = new MinisatInterfacingNewSimp(_opt,true);
  }catch(Minisat::OutOfMemoryException&){
    MinisatInterfacingNewSimp::reportMinisatOutOfMemory();
  }

  /*
  if(_opt.satSolver() != Options::SatSolver::MINISAT){
    cout << "Warning: overriding sat solver for FMB, using minisat" << endl;
  }
  */
/*
  switch(_opt.satSolver()){
#if VZ3
    case Options::SatSolver::Z3:
        ASSERTION_VIOLATION_REP("Do not use fmb with Z3");
#endif
    case Options::SatSolver::MINISAT:
        try{
          _solver = new MinisatInterfacingNewSimp(_opt,true);
        }catch(Minisat::OutOfMemoryException&){
          MinisatInterfacingNewSimp::reportMinisatOutOfMemory();
        }
      break;
    default:
      ASSERTION_VIOLATION_REP(_opt.satSolver());
  }
*/

  // set the number of SAT variables, this could cause an exception
  _solver->ensureVarCount(offsets-1);

  // needs to be redone for each size as we use this to pick the number of
  // things to order and the constants to ground with 
  createSymmetryOrdering();

  return true;
}

// Compare function symbols by their usage in the problem
struct FMBSymmetryFunctionComparator
{
  static Comparison compare(unsigned f1, unsigned f2)
  {
    unsigned c1 = env.signature->getFunction(f1)->usageCnt();
    unsigned c2 = env.signature->getFunction(f2)->usageCnt();
    return Int::compare(c2,c1);
  }
};

void FiniteModelBuilder::createSymmetryOrdering()
{
  CALL("FiniteModelBuilder::createSymmeteryOrdreing");
  
  // only really required the first time
  _sortedGroundedTerms.ensure(_sortedSignature->sorts);

  // Build up an ordering of GroundedTerms per sort
  for(unsigned s=0;s<_sortedSignature->sorts;s++){
    unsigned size = _sortModelSizes[s];

    // Remove any previously computed ordering
    _sortedGroundedTerms[s].reset();

    // Add all the constants of that sort
    for(unsigned c=0;c<_sortedSignature->sortedConstants[s].length();c++){
      GroundedTerm g;
      g.f = _sortedSignature->sortedConstants[s][c];
      g.grounding.ensure(0); // no grounding needed
      _sortedGroundedTerms[s].push(g);
      //cout << "Adding " << g.toString()  << " to " << s << endl;
    }

    // Next add some groundings of function symbols
    // Currently these will be uniform groundings i.e. if we have arity 2 then we consider f(1,1),f(2,2)
    // TODO also allow f(1,2) and f(2,1)
    bool arg_first = false;
    switch(env.options->fmbSymmetryWidgetOrders()){
    // If function first then we do each function in turn i.e.
    // f(1)f(2)f(3)g(1)g(2)g(3)
    case Options::FMBWidgetOrders::FUNCTION_FIRST:
    {
      for(unsigned f=0;f<_sortedSignature->sortedFunctions[s].length();f++){
        for(unsigned m=1;m<=size;m++){

          GroundedTerm g;
          g.f =_sortedSignature->sortedFunctions[s][f];

          // We skip f if its range is bounded to less than size
          unsigned arity = env.signature->functionArity(g.f);
          unsigned gfsrt = _sortedSignature->functionSignatures[g.f][arity];
          if(_sortedSignature->sortBounds[gfsrt] < size) continue;

          g.grounding.ensure(arity);

          // We skip f if its domain is bounded to less than g.grounding
          bool outOfBounds = false;
          for(unsigned i=0;i<arity;i++){
            unsigned srtx = _sortedSignature->functionSignatures[g.f][i];
            g.grounding[i] = min(m,_sortModelSizes[srtx]);
            if(_sortedSignature->sortBounds[srtx] < g.grounding[i])
              outOfBounds=true;
          }
          if(outOfBounds) continue;

          _sortedGroundedTerms[s].push(g);
          //cout << "Adding " << g.toString() <<  " to " << s << endl;
        }
      }
      break;
    }
    // If argument first then we do each size and then each function i.e.
    // f(1)g(1)f(2)g(2)f(3)g(3)
    case Options::FMBWidgetOrders::ARGUMENT_FIRST:
      arg_first=true;
      // now use diagional code but don't do the diagonal

    // If diagonal then we do f(1)g(2)h(3)f(2)g(3)h(1)f(3)g(1)h(2)
    case Options::FMBWidgetOrders::DIAGONAL:
    {
      for(unsigned m=1;m<=size;m++){
        for(unsigned f=0;f<_sortedSignature->sortedFunctions[s].length();f++){

          GroundedTerm g;
          g.f =_sortedSignature->sortedFunctions[s][f];

          // We skip f if its range is bounded to less than size
          unsigned arity = env.signature->functionArity(g.f);
          unsigned gfsrt = _sortedSignature->functionSignatures[g.f][arity];
          if(_sortedSignature->sortBounds[gfsrt] < size) continue;

          // If doing arg_first then we ignore the diagonal thing
          // otherwise the grounding is this weird function of m, f and size
          unsigned groundWith = arg_first ? m : 1+((m+f)%(size));
          g.grounding.ensure(arity);

          // We skip f if its domain is bounded to less than g.grounding
          bool outOfBounds = false;
          for(unsigned i=0;i<arity;i++){
            unsigned srtx = _sortedSignature->functionSignatures[g.f][i];
            g.grounding[i] = min(groundWith,_sortModelSizes[srtx]);
            if(_sortedSignature->sortBounds[srtx] < g.grounding[i])
              outOfBounds=true;
          }
          if(outOfBounds) continue;
  
          _sortedGroundedTerms[s].push(g);
          //cout << "Adding " << g.toString() << " to " << s << endl;
        }
      }
    }
    }

  }
}

// Initialise things for the first time
void FiniteModelBuilder::init()
{
  CALL("FiniteModelBuilder::init");

  // If we're not complete don't both doing anything
  if(!_isAppropriate) return;

  if(!_prb.units()) return;

  env.statistics->phase = Statistics::FMB_PREPROCESSING;

  
  Stack<DHSet<unsigned>*> equivalent_vampire_sorts; 
  DHSet<std::pair<unsigned,unsigned>> vampire_sort_constraints_nonstrict;
  DHSet<std::pair<unsigned,unsigned>> vampire_sort_constraints_strict;
  if(env.options->fmbDetectSortBounds()){
    FunctionRelationshipInference inf;
    inf.findFunctionRelationships(
      _prb.clauseIterator(),
      equivalent_vampire_sorts,
      vampire_sort_constraints_nonstrict,
      vampire_sort_constraints_strict); 
  }

  ClauseList* clist = 0;
  if(env.options->fmbAdjustSorts() == Options::FMBAdjustSorts::PREDICATE){
    DArray<unsigned> deleted_functions(env.signature->functions());
    for(unsigned f=0;f<env.signature->functions();f++){
      deleted_functions[f] = _deletedFunctions.find(f) || env.signature->getFunction(f)->usageCnt()==0;
     }
    ClauseList::pushFromIterator(_prb.clauseIterator(),clist);
    Monotonicity::addSortPredicates(true, clist,deleted_functions);
  }
  if(env.options->fmbAdjustSorts() == Options::FMBAdjustSorts::FUNCTION){ 
    ClauseList::pushFromIterator(_prb.clauseIterator(),clist);
    Monotonicity::addSortFunctions(true,clist);
  }


  // Perform DefinitionIntroduction as we iterate
  // over the clauses of the problem
  DefinitionIntroduction cit = DefinitionIntroduction(
    (clist ? pvi(ClauseList::Iterator(clist)) : _prb.clauseIterator())
  );

  // Store distinct constants by type
  DArray<DHMap<unsigned,DHSet<unsigned>*>*> _distinctConstants;
  _distinctConstants.ensure(env.signature->typeCons());
  for(unsigned i=0;i<env.signature->typeCons();i++){ _distinctConstants[i]=0; }

  // Apply flattening and split clauses into ground and non-ground
  while(cit.hasNext()){
    Clause* c = cit.next();

    // Do we have a ground unit equality between constants?
    if(c->length()==1 && c->varCnt()==0){
      Literal* l = (*c)[0];
      if(l->isEquality() && l->isNegative()){
        TermList* left = l->nthArgument(0);
        TermList* right = l->nthArgument(1);

        if(left==right){
          // we have discovered unsat
          throw RefutationFoundException(c);
        }

        if(left->isTerm() && left->term()->arity()==0 &&
           right->isTerm() && right->term()->arity()==0){

          TermList srtT = SortHelper::getResultSort(left->term());
          unsigned srt = srtT.term()->functor();
          auto map = _distinctConstants[srt];
          if(map==0){
            map = new DHMap<unsigned,DHSet<unsigned>*>();
            _distinctConstants[srt]=map;
          }
          unsigned lnum = left->term()->functor();
          unsigned rnum = right->term()->functor();
          {
            DHSet<unsigned>* set;
            if(!map->find(lnum,set)){
              set = new DHSet<unsigned>();
              map->insert(lnum,set);
            }
            set->insert(rnum);
          }
          {
            DHSet<unsigned>* set;
            if(!map->find(rnum,set)){
              set = new DHSet<unsigned>();
              map->insert(rnum,set);
            }
            set->insert(lnum);
          } 
        }
      }
    }

#if VTRACE_FMB
    //cout << "Flatten " << c->toString() << endl;
#endif
    c = ClauseFlattening::flatten(c);
#if VTRACE_FMB
    //cout << "Flattened " << c->toString() << endl;
#endif
    ASS(c);

    if(isRefutation(c)){
      throw RefutationFoundException(c);
    }

    if(c->varCnt()==0){
#if VTRACE_FMB
      //cout << "Add ground clause " << c->toString() << endl;
#endif
      ClauseList::push(c, _groundClauses);
    }else{
#if VTRACE_FMB
    //cout << "Add non-ground clause " << c->toString() << endl;
#endif
      ClauseList::push(c, _clauses);

    }
  }
  if(!_clauses){
    if(outputAllowed()){
      cout << "The problem is propositional so there are no sorts!" << endl;
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

  // TODO: consider updating usage count by rescanning property
  // in particular, terms replaced by definitions have disappeared!
  
  // TODO: consider updating usage count by rescanning property as we have had to 
  //       OR ensure that usage count is updated for any introduced symbols e.g. in Monotonicity

  // record the deleted functions and predicates
  // we do this here so that there are slots for symbols introduce in previous
  // preprocessing steps (definition introduction, splitting)
  del_f.ensure(env.signature->functions());
  del_p.ensure(env.signature->predicates());

  for(unsigned f=0;f<env.signature->functions();f++){
    del_f[f] = _deletedFunctions.find(f) || env.signature->getFunction(f)->usageCnt()==0;
#if VTRACE_FMB
    if(del_f[f]) cout << "Mark " << env.signature->functionName(f)  << " as deleted" << endl;
#endif
  }
  for(unsigned p=0;p<env.signature->predicates();p++){
    del_p[p] = (_deletedPredicates.find(p) || _trivialPredicates.find(p));
#if VTRACE_FMB
    if(del_p[p]) cout << "Mark " << env.signature->predicateName(p) << " as deleted" << endl;
#endif
  }

#if VTRACE_FMB
  cout << "Performing Sort Inference" << endl;
#endif

  // perform SortInference on ground and non-ground clauses
  // preprocessing should preserve sorts and doing this here means that introduced symbols get sorts
  {
    TimeCounter tc(TC_FMB_SORT_INFERENCE);
    //ClauseList* both = ClauseList::concat(_clauses,_groundClauses);
    SortInference inference(_clauses,del_f,del_p,equivalent_vampire_sorts,_distinct_sort_constraints);
    inference.doInference();
    _sortedSignature = inference.getSignature(); 
    ASS(_sortedSignature);
#if VTRACE_FMB
    cout << "Done sort inference" << endl;
#endif

    // now we have a mapping between vampire sorts and distinct sorts we can translate
    // the sort constraints, if any
    {
      DHSet<std::pair<unsigned,unsigned>>::Iterator it(vampire_sort_constraints_nonstrict); 
      while(it.hasNext()){
        std::pair<unsigned,unsigned> vconstraint = it.next();
        ASS(_sortedSignature->vampireToDistinctParent.find(vconstraint.first));
        ASS(_sortedSignature->vampireToDistinctParent.find(vconstraint.second));
        //cout << "constraint " << vconstraint.first << " , " << vconstraint.second << endl;
        unsigned s1 = _sortedSignature->vampireToDistinctParent.get(vconstraint.first);
        unsigned s2 = _sortedSignature->vampireToDistinctParent.get(vconstraint.second);
        //cout << "is " << s1 << " , " << s2 << endl;
        _distinct_sort_constraints.push(make_pair(s1,s2));
      }
    }
    {
      DHSet<std::pair<unsigned,unsigned>>::Iterator it(vampire_sort_constraints_strict);
      while(it.hasNext()){
        std::pair<unsigned,unsigned> vconstraint = it.next();
        ASS(_sortedSignature->vampireToDistinctParent.find(vconstraint.first));
        ASS(_sortedSignature->vampireToDistinctParent.find(vconstraint.second));
        //cout << "strict constraint " << vconstraint.first << " , " << vconstraint.second << endl;
        unsigned s1 = _sortedSignature->vampireToDistinctParent.get(vconstraint.first);
        unsigned s2 = _sortedSignature->vampireToDistinctParent.get(vconstraint.second);
        //cout << "is " << s1 << " , " << s2 << endl;
        _strict_distinct_sort_constraints.push(make_pair(s1,s2));
      }
    }

#if VTRACE_FMB
  cout << "Finding Min and Max Sort Sizes" << endl;
#endif

    // Record the maximum sort sizes detected during sort inference 
    _distinctSortMaxs.ensure(_sortedSignature->distinctSorts);
    _distinctSortMins.ensure(_sortedSignature->distinctSorts);
    for(unsigned s=0;s<_sortedSignature->distinctSorts;s++){ 
      _distinctSortMaxs[s]=UINT_MAX; 
      _distinctSortMins[s]=1;
    }

    DArray<unsigned> bfromSI(_sortedSignature->distinctSorts);
    DArray<unsigned> dConstants(_sortedSignature->distinctSorts);
    DArray<unsigned> dFunctions(_sortedSignature->distinctSorts);
    for(unsigned s=0;s<_sortedSignature->distinctSorts;s++){ 
      bfromSI[s]=0;
      dConstants[s]=0;
      dFunctions[s]=0;
    }

    for(unsigned s=0;s<_sortedSignature->sorts;s++){
      unsigned bound = _sortedSignature->sortBounds[s];
      unsigned parent = _sortedSignature->parents[s];
      if(bound > bfromSI[parent]){ bfromSI[parent]=bound; }
      dConstants[parent] += (_sortedSignature->sortedConstants[s]).size();
      dFunctions[parent] += (_sortedSignature->sortedFunctions[s]).size();
    }
    for(unsigned s=0;s<_sortedSignature->distinctSorts;s++){ 
      _distinctSortMaxs[s] = min(_distinctSortMaxs[s],bfromSI[s]); 
    }


    for(unsigned s=0;s<_sortedSignature->distinctSorts;s++){
      bool epr = env.property->category()==Property::EPR
                 // if we have no functions we are epr in this sort
                 || dFunctions[s]==0; 
      if(epr){
        unsigned c = dConstants[s]; 
        if(c==0) continue; //size of 0 does not make sense... maybe we should set it to 1 here? TODO
        // TODO not sure about this second condition, if c < current max what would happen?
        // why are we looking for the 'biggest' max?
        if(_distinctSortMaxs[s]==UINT_MAX || c > _distinctSortMaxs[s]){
          _distinctSortMaxs[s]=c;
        }
      }
    }

    // if we've done the sort expansion thing then the max for the parent should be
    // the max of all children
    for(unsigned s=0;s<env.signature->typeCons();s++){
      if((env.property->usesSort(s) || env.signature->isNonDefaultCon(s)) && _sortedSignature->vampireToDistinct.find(s)){
        Stack<unsigned>* dmembers = _sortedSignature->vampireToDistinct.get(s);
        ASS(dmembers);
        if(dmembers->size() > 1){ 
          unsigned parent = _sortedSignature->vampireToDistinctParent.get(s);
          Stack<unsigned>::Iterator children(*dmembers);
          while(children.hasNext()){
            unsigned child = children.next();
            if(child==parent) continue;
            //cout << "max of " << parent << " inherets child " << child << endl;
            _distinctSortMaxs[parent] = max(_distinctSortMaxs[parent],_distinctSortMaxs[child]);
          }
        }
      }
    }

    //_distinctConstants
    for(unsigned s=0;s<env.signature->typeCons();s++){
      if(_distinctConstants[s]!=0){

        ASS(_sortedSignature->vampireToDistinct.find(s));
        auto map = _distinctConstants[s];
        unsigned max = CliqueFinder::findMaxCliqueSize(map);
        Stack<unsigned>* dss = _sortedSignature->vampireToDistinct.get(s);
        Stack<unsigned>::Iterator ds(*dss);
        while(ds.hasNext()){
          _distinctSortMins[ds.next()]=max;
        }
#if VTRACE_FMB
        cout << "Setting min for " << env.signature->typeConName(s) << " to " << max << endl;
#endif
      }
    }

#if VTRACE_FMB
  cout << "Optionally doing Symmetry Ordering precomputation" << endl;
#endif

    // If symmetry ordering uses the usage after preprocessing then recompute symbol usage
    // Otherwise this was done at clausification
    if(env.options->fmbSymmetryOrderSymbols() != Options::FMBSymbolOrders::PREPROCESSED_USAGE){
     // reset usage counts
     for(unsigned f=0;f<env.signature->functions();f++){
       env.signature->getFunction(f)->resetUsageCnt();
     }
     // do them again!
     {
       ClauseIterator cit = pvi(ClauseList::Iterator(_clauses));
       while(cit.hasNext()){
         Clause* c = cit.next();
         // Can assume c is flat, so no nesting :)
         for(unsigned i=0;i<c->length();i++){
           Literal* l = (*c)[i];
            // Let's only count usage of functions (not predicates) as that's all we use
           if(l->isEquality() && !l->isTwoVarEquality()){
             ASS(!l->nthArgument(0)->isVar());
             ASS(l->nthArgument(1)->isVar());
             Term* t = l->nthArgument(0)->term();
             unsigned f = t->functor();
             env.signature->getFunction(f)->incUsageCnt();
           }
         }
       }
     }
    }

    // Fragile, change if extend FMBSymbolOrders as it assumes that the values that
    //          are not occurence depend on usage (as per FMBSymmetryFunctionComparator)
    if(env.options->fmbSymmetryOrderSymbols() != Options::FMBSymbolOrders::OCCURENCE){
      // Let's try sorting constants and functions in the sorted signature
      for(unsigned s=0;s<_sortedSignature->sorts;s++){
        Stack<unsigned> sortedConstants =  _sortedSignature->sortedConstants[s];
        Stack<unsigned> sortedFunctions = _sortedSignature->sortedFunctions[s];
        sort<FMBSymmetryFunctionComparator>(sortedConstants.begin(),sortedConstants.end());
        sort<FMBSymmetryFunctionComparator>(sortedFunctions.begin(),sortedFunctions.end());
      }
    }
  }

#if VTRACE_FMB
  cout << "Now Find Minimum Sort Bounds" << endl;
#endif

  //TODO why is this here? Can intermediate steps introduce new functions?
  //  - SortInference can introduce new constants
  del_f.expand(env.signature->functions());

  // these offsets are for SAT variables and need to be set to the right size
  f_offsets.ensure(env.signature->functions());
  p_offsets.ensure(env.signature->predicates());

  // Set up fminbound, which records the minimum sort size for a function symbol
  // i.e. the smallest return or parameter sort
  // this loop also counts the number of constants in the problem
  _distinctSortConstantCount.ensure(_sortedSignature->distinctSorts);
  _fminbound.ensure(env.signature->functions());
  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;

    if(env.signature->functionArity(f)==0){ 
      TermList vsrtT = env.signature->getFunction(f)->fnType()->result();
      if(!vsrtT.isBoolSort()){
        unsigned vsrt = vsrtT.term()->functor();
        ASS(_sortedSignature->vampireToDistinctParent.find(vsrt));
        unsigned dsrt = _sortedSignature->vampireToDistinctParent.get(vsrt);
        _distinctSortConstantCount[dsrt]++;
      }
    }

    // f might have been added to the signature since we created the sortedSignature
    // TODO how?
    if(f >= _sortedSignature->functionSignatures.size()){
      _fminbound[f]=UINT_MAX;
      continue;
    }
    const DArray<unsigned>& fsig = _sortedSignature->functionSignatures[f];
    unsigned min = _sortedSignature->sortBounds[fsig[0]];
    for(unsigned i=1;i<fsig.size();i++){
      unsigned sz = _sortedSignature->sortBounds[fsig[i]];
      if(sz<min) min = sz;
      }
    _fminbound[f]=min;
  }

#if VTRACE_FMB
  cout << "Set up Clause Signatures" << endl;
#endif

  //Set up clause signature
  //cout << "Setting up clause sigs" << endl;
  {
    ClauseList::Iterator cit(_clauses);
    while(cit.hasNext()){
      Clause* c = cit.next();
#if VTRACE_FMB
      cout << "CLAUSE " << c->toString() << endl;  
#endif
      // will record the sorts for each variable in the clause 
      // note that clauses have been normalized so variables go from 0 to varCnt
      DArray<unsigned>* csig = new DArray<unsigned>(c->varCnt()); 
      DArray<bool> csig_set(c->varCnt());
      for(unsigned i=0;i<c->varCnt();i++) csig_set[i]=false;
      static Stack<Literal*> twoVarEqualities;
      twoVarEqualities.reset();
      for(unsigned i=0;i<c->length();i++){
        Literal* lit = (*c)[i];
        if(lit->isEquality()){
          if(lit->isTwoVarEquality()){
             twoVarEqualities.push(lit);
             continue;
          }
          ASS(lit->nthArgument(0)->isTerm());
          ASS(lit->nthArgument(1)->isVar());
          Term* t = lit->nthArgument(0)->term();
          ASS(!del_f[t->functor()]);
          const DArray<unsigned>& fsg = _sortedSignature->functionSignatures[t->functor()];
          ASS_REP(fsg.size() == env.signature->functionArity(t->functor())+1,  fsg.size());
          unsigned var = lit->nthArgument(1)->var();
          unsigned ret = fsg[env.signature->functionArity(t->functor())];
          if(csig_set[var]){ ASS_EQ((*csig)[var],ret); }
          else{ 
            (*csig)[var]=ret;
            csig_set[var]=true;
          }
          for(unsigned j=0;j<t->arity();j++){
            ASS(t->nthArgument(j)->isVar());
            unsigned asrt = fsg[j]; 
            unsigned avar = (t->nthArgument(j))->var();
            ASS(avar < csig->size());
            if(!csig_set[var]){ ASS((*csig)[avar]==asrt); }
            else{ 
              (*csig)[avar]=asrt;
              csig_set[avar]=true;
            }
          }
        }
        else{
          ASS_EQ(lit->arity(),env.signature->predicateArity(lit->functor()));
          for(unsigned j=0;j<lit->arity();j++){
            ASS(lit->nthArgument(j)->isVar());
            unsigned asrt = _sortedSignature->predicateSignatures[lit->functor()][j];
            unsigned avar = (lit->nthArgument(j))->var();
            if(csig_set[avar]){ ASS((*csig)[avar]==asrt); }
            else{ 
              (*csig)[avar]=asrt;
              csig_set[avar]=true;
            }
          }
        }
      }
      Stack<Literal*>::Iterator tvit(twoVarEqualities);
      while(tvit.hasNext()){
        Literal* lit = tvit.next();
        ASS(lit->isTwoVarEquality());
        unsigned var1 = lit->nthArgument(0)->var();
        unsigned var2 = lit->nthArgument(1)->var();
        //cout << var1 << " and " << var2 << endl;
        if(csig_set[var1]){
          if(csig_set[var2]){
            // This is a special edge case where we process a two-var equality before having
            // enough information, see below
            if((*csig)[var1] != (*csig)[var2]){
              TermList litSort = lit->twoVarEqSort();
              unsigned litSortU = litSort.term()->functor();
              unsigned dsort = _sortedSignature->vampireToDistinctParent.get(litSortU);
              unsigned sort = _sortedSignature->varEqSorts[dsort];
              ASS((*csig)[var1] == sort || (*csig)[var2] == sort);
              if((*csig)[var1] == sort){ (*csig)[var1] = (*csig)[var2]; }
              else{ (*csig)[var2] = (*csig)[var1]; } 
            }
          }
          else{ 
            (*csig)[var2] = (*csig)[var1]; 
            csig_set[var2]=true;
          }
        }
        else if(csig_set[var2]){
          (*csig)[var1] = (*csig)[var2];
          csig_set[var1]=true;
        }
        else{ 
          // At this point I have a two-variable equality where those variables do not
          // tell me what sorts they should have by appearance in a function or predicate symbol
          // So I use the special sort for this
          TermList litSort = lit->twoVarEqSort();
          unsigned litSortU = litSort.term()->functor();
          unsigned dsort = _sortedSignature->vampireToDistinctParent.get(litSortU);
          unsigned sort = _sortedSignature->varEqSorts[dsort];
          (*csig)[var1] = sort;
          (*csig)[var2] = sort;
          csig_set[var1]=true;
          csig_set[var2]=true;
          // NOTE - we might later  find out that the special sort wasn't necessary  e.g.
          // if we have X0 = X1 | X1 = X2 | p(X2) we may first give special sort to X0 and X1
          // but then replace this by the sort of X2 when we  process  X1 = X2
        }
      }

#if VDEBUG
      for(unsigned i=0;i<csig->size();i++){
        ASS_REP(csig_set[i],c->toString());
      }
#endif
      _clauseVariableSorts.insert(c,csig);
      //cout << "done" << endl;
    } 
  }
} // init()

void FiniteModelBuilder::addGroundClauses()
{
  CALL("FiniteModelBuilder::addGroundClauses");

  // If we don't have any ground clauses don't do anything
  if(!_groundClauses) return;

  ClauseList::Iterator cit(_groundClauses);

  // Note ground clauses will consist of propositional symbols only due to flattening
  static const DArray<unsigned> emptyGrounding(0);
  while(cit.hasNext()){

      Clause* c = cit.next();
      ASS(c);

      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
      for(unsigned i=0;i<c->length();i++){
        unsigned f = (*c)[i]->functor();
        SATLiteral slit = getSATLiteral(f,emptyGrounding,(*c)[i]->polarity(),false);
        satClauseLits.push(slit);
      }
      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
  }
}

// uses _distinctSortSizes to estimate how many instances would we generate
unsigned FiniteModelBuilder::estimateInstanceCount()
{
  CALL("FiniteModelBuilder::estimateInstanceCount");
  unsigned res = 0;
  ClauseList::Iterator cit(_clauses);

  while(cit.hasNext()){
    unsigned instances = 1;

    Clause* c = cit.next();
    unsigned vars = c->varCnt();
    const DArray<unsigned>* varSorts = _clauseVariableSorts.get(c) ;
    if(!varSorts){
      continue;
    }

    for(unsigned var=0;var<vars;var++){
      unsigned srt = (*varSorts)[var];
      instances *= min(_distinctSortSizes[_sortedSignature->parents[srt]],_sortedSignature->sortBounds[srt]);
    }

    res += instances;
  }
  return res;
}

void FiniteModelBuilder::addNewInstances()
{
  CALL("FiniteModelBuilder::addNewInstances");

  ClauseList::Iterator cit(_clauses); 

  while(cit.hasNext()){
    Clause* c = cit.next();
    ASS(c);
#if VTRACE_FMB
    cout << "Instances of " << c->toString() << endl;
#endif

    unsigned vars = c->varCnt();
    const DArray<unsigned>* varSorts = _clauseVariableSorts.get(c) ;
    static DArray<unsigned> maxVarSize;
    maxVarSize.ensure(vars);

    if(!varSorts){
      // this means that the clause consists only of variable equalities
      // earlier we ensured that such clauses have at least one positive
      // variable equality, therefore they can always be satisfied
      // so we skip this clause 
      // TODO should it be removed earlier?
      continue;
    }
    ASS(varSorts);

    static ArrayMap<unsigned> varDistinctSortsMaxes(_distinctSortSizes.size());

    if (!_xmass) {
      varDistinctSortsMaxes.reset();
    }

    //cout << "maxVarSizes "<<endl;;
    for(unsigned var=0;var<vars;var++) {
      unsigned srt = (*varSorts)[var];
      //cout << "srt="<<srt;
      maxVarSize[var] = min(_sortModelSizes[srt],_sortedSignature->sortBounds[srt]);
      //cout << ",max="<<maxVarSize[var] << endl;

      if (!_xmass) {
        unsigned dsort = _sortedSignature->parents[srt];
        if (!_sortedSignature->monotonicSorts[dsort]) { // don't mark instances of monotonic sorts!
          varDistinctSortsMaxes.set(dsort,1);
        }
      }
    }
    
    static DArray<unsigned> grounding;
    grounding.ensure(vars);

    for(unsigned i=0;i<vars;i++) grounding[i]=1;
    grounding[vars-1]=0;

instanceLabel:
    for(unsigned var=vars-1;var+1!=0;var--){
     
      //Checking against mins skips instances where sort size restricts it
      if(grounding[var]==maxVarSize[var]){
        grounding[var]=1;
      } 
      else{
        grounding[var]++;
        // Grounding represents a new instance
        static SATLiteralStack satClauseLits;
        satClauseLits.reset();

        if (_xmass) {
          varDistinctSortsMaxes.reset();
          for(unsigned var=0;var<vars;var++) {
            // cout << " var" << var;
            unsigned srt = (*varSorts)[var];
            // cout << " srt" << srt;
            unsigned dsr = _sortedSignature->parents[srt];
            // cout << " dsr" << dsr;

            if (_sortedSignature->monotonicSorts[dsr]) {
              continue;
            }

            unsigned prev = varDistinctSortsMaxes.get(dsr,0);
            // cout << " prev" << prev;

            unsigned cur = grounding[var];
            // cout << " cur" << cur;

            varDistinctSortsMaxes.set(dsr,max(cur,prev));

            // cout << endl;
          }

          // start by adding the sort markers
          for (unsigned i = 0; i < _distinctSortSizes.size(); i++) {
            unsigned val = varDistinctSortsMaxes.get(i,0);

            if (val > 1) {
              // cout << "Marking sort " << i << " with " << val-2 << " negative" << endl;
              satClauseLits.push(SATLiteral(marker_offsets[i]+val-2,0));
            }
          }
          // cout << "Clause finised" << endl;
        } else {
          for (unsigned i = 0; i < _distinctSortSizes.size(); i++) {
            if (varDistinctSortsMaxes.get(i,0)) {
              satClauseLits.push(SATLiteral(instancesMarker_offset+i,0));
            }
          }
        }

        // Ground and translate each literal into a SATLiteral
        for(unsigned lindex=0;lindex<c->length();lindex++){
          Literal* lit = (*c)[lindex];

          // check cases where literal is x=y
          if(lit->isTwoVarEquality()){
            bool equal = grounding[lit->nthArgument(0)->var()] == grounding[lit->nthArgument(1)->var()]; 
            if((lit->isPositive() && equal) || (!lit->isPositive() && !equal)){
              //Skip instance
              goto instanceLabel; 
            } 
            if((lit->isPositive() && !equal) || (!lit->isPositive() && equal)){
              //Skip literal
              continue;
            }
          }
          if(lit->isEquality()){
            ASS(lit->nthArgument(0)->isTerm());
            ASS(lit->nthArgument(1)->isVar());
            Term* t = lit->nthArgument(0)->term();
            unsigned functor = t->functor();
            unsigned arity = t->arity();
            static DArray<unsigned> use;
            use.ensure(arity+1);

            for(unsigned j=0;j<arity;j++){
              ASS(t->nthArgument(j)->isVar());
              use[j] = grounding[t->nthArgument(j)->var()];
            }
            use[arity]=grounding[lit->nthArgument(1)->var()];
            satClauseLits.push(getSATLiteral(functor,use,lit->polarity(),true));
            
          }else{
            unsigned functor = lit->functor();
            unsigned arity = lit->arity();
            static DArray<unsigned> use;
            use.ensure(arity);

            for(unsigned j=0;j<arity;j++){
              ASS(lit->nthArgument(j)->isVar());
              use[j] = grounding[lit->nthArgument(j)->var()];
            }
            satClauseLits.push(getSATLiteral(functor,use,lit->polarity(),false));
          }
        }
     
        SATClause* satCl = SATClause::fromStack(satClauseLits);
        addSATClause(satCl);

        goto instanceLabel;
      }
    }
  }
}

// uses _distinctSortSizes to estimate how many instances would we generate
unsigned FiniteModelBuilder::estimateFunctionalDefCount()
{
  CALL("FiniteModelBuilder::estimateFunctionalDefCount");
  unsigned res = 0;

  for(unsigned f=0;f<env.signature->functions();f++){
    unsigned instances = 1;

    if(del_f[f]) continue;
    unsigned arity = env.signature->functionArity(f);

    const DArray<unsigned>& f_signature = _sortedSignature->functionSignatures[f];

    // find max size of y and z
    unsigned returnSrt = f_signature[arity];
    instances *= min(_sortedSignature->sortBounds[returnSrt],_distinctSortSizes[_sortedSignature->parents[returnSrt]]);
    instances *= min(_sortedSignature->sortBounds[returnSrt],_distinctSortSizes[_sortedSignature->parents[returnSrt]]);

    // we skip 0 and 1 as these are y and z
    for(unsigned var=2;var<arity+2;var++){
      unsigned srt = f_signature[var-2]; // f_signature[arity] is return sort
      instances *= min(_sortedSignature->sortBounds[srt],_distinctSortSizes[_sortedSignature->parents[srt]]);
    }

    res += instances / 2;
  }
  return res;
}

void FiniteModelBuilder::addNewFunctionalDefs()
{
  CALL("FiniteModelBuilder::addNewFunctionalDefs");

  // For each function f of arity n we add the constraint 
  // f(x1,...,xn) != y | f(x1,...,xn) != z 
  // they should be instantiated with groundings where y!=z

  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;
    unsigned arity = env.signature->functionArity(f);

#if VTRACE_FMB
    cout << "Adding func defs for " << env.signature->functionName(f) << endl;
#endif

    const DArray<unsigned>& f_signature = _sortedSignature->functionSignatures[f];
    static DArray<unsigned> maxVarSize;
    maxVarSize.ensure(arity+2);

    // find max size of y and z 
    unsigned returnSrt = f_signature[arity];
    maxVarSize[0] = min(_sortedSignature->sortBounds[returnSrt],_sortModelSizes[returnSrt]);
    maxVarSize[1] = min(_sortedSignature->sortBounds[returnSrt],_sortModelSizes[returnSrt]);

    // we skip 0 and 1 as these are y and z
    for(unsigned var=2;var<arity+2;var++){
      unsigned srt = f_signature[var-2]; // f_signature[arity] is return sort
      maxVarSize[var] = min(_sortedSignature->sortBounds[srt],_sortModelSizes[srt]);
    }

    static DArray<unsigned> grounding;
    grounding.ensure(arity+2);
    for(unsigned var=0;var<arity+2;var++){ grounding[var]=1; }
    grounding[arity+1]=0;

newFuncLabel:
      for(unsigned var=arity+1;var+1!=0;var--){

        if(grounding[var]==maxVarSize[var]){
          grounding[var]=1;
        }
        else{
          grounding[var]++;
          //cout << "Grounding: ";
          //for(unsigned j=0;j<grounding.size();j++) cout << grounding[j] << " ";
          //cout << endl;

          // we only need to consider the non-symmetric cases where y >= z
          if(grounding[0]>=grounding[1]){
            //Skip this instance
            goto newFuncLabel;
          }
          static SATLiteralStack satClauseLits;
          satClauseLits.reset();

          // grounding is of the form [y,z,x1,x2,...]
          // but use wants to be of the form use[x1,x2,...,y] and use[x1,x2,....,z]
          // so need to do some moving around!
          // btw we put y and z at the front so we can do the symmetry trick above
          static DArray<unsigned> use;
          use.ensure(arity+1);
          for(unsigned k=0;k<arity;k++) use[k]=grounding[k+2];
          use[arity]=grounding[0];
          satClauseLits.push(getSATLiteral(f,use,false,true)); 
          use[arity]=grounding[1];
          satClauseLits.push(getSATLiteral(f,use,false,true)); 

          SATClause* satCl = SATClause::fromStack(satClauseLits);
          addSATClause(satCl);
          goto newFuncLabel;
        }
      }
  }
}

void FiniteModelBuilder::addNewSymmetryOrderingAxioms(unsigned size,
                       Stack<GroundedTerm>& groundedTerms)
{
  CALL("FiniteModelBuilder::addNewSymmetryOrderingAxioms");


  // Add restricted totality 
  // i.e. for constant a1 add { a1=1 } and for a2 add { a2=1, a2=2 } and so on
  if(groundedTerms.length() < size) return;

  GroundedTerm gt = groundedTerms[size-1];

  unsigned arity = env.signature->functionArity(gt.f);
  static DArray<unsigned> grounding;
  grounding.ensure(arity+1);
  for(unsigned i=0;i<arity;i++) grounding[i] = gt.grounding[i];

  //cout << "Add symmetry ordering for " << gt.toString() << endl;

  static SATLiteralStack satClauseLits;
  satClauseLits.reset(); 
  for(unsigned i=1;i<=size;i++){
    grounding[arity]=i;
    SATLiteral sl = getSATLiteral(gt.f,grounding,true,true);
    satClauseLits.push(sl);
  }
  SATClause* satCl = SATClause::fromStack(satClauseLits);
  addSATClause(satCl);

}

void FiniteModelBuilder::addNewSymmetryCanonicityAxioms(unsigned size,
                       Stack<GroundedTerm>& groundedTerms,
                       unsigned maxSize)
{
  CALL("FiniteModelBuilder::addNewSymmetryCanonicityAxioms");

  if(size<=1) return;

  unsigned w = _symmetryRatio * maxSize; 
  if(w > groundedTerms.length()){
     w = groundedTerms.length();
  }

  for(unsigned i=1;i<w;i++){
      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
   
      GroundedTerm gti = groundedTerms[i];
      unsigned arityi = env.signature->functionArity(gti.f);

      if(arityi>0) return;

      static DArray<unsigned> grounding_i;
      grounding_i.ensure(arityi+1);
      for(unsigned a=0;a<arityi;a++){ grounding_i[a]=gti.grounding[a];}
      grounding_i[arityi]=size;
      satClauseLits.push(getSATLiteral(gti.f,grounding_i,false,true));
 
      //cout << "Adding cannon for " << gti.toString() << endl;

      for(unsigned j=0;j<i;j++){
        GroundedTerm gtj = groundedTerms[j];
        unsigned arityj = env.signature->functionArity(gtj.f);
        static DArray<unsigned> grounding_j;
        grounding_j.ensure(arityj+1);
        for(unsigned a=0;a<arityj;a++){ grounding_j[a]=gtj.grounding[a];}
        grounding_j[arityj]=size-1;
        //cout << "with " <<gtj.toString()<<endl;

        satClauseLits.push(getSATLiteral(gtj.f,grounding_j,true,true));
      }
      addSATClause(SATClause::fromStack(satClauseLits));
  }

}

void FiniteModelBuilder::addUseModelSize(unsigned size)
{
  CALL("FiniteModelBuilder::addUseModelSize");

  return;
/*

  // Only do thise if we have unary functions at most
  if(_maxArity>1) return;

  static SATLiteralStack satClauseLits;
  satClauseLits.reset();

  for(unsigned s=0;s<_sortedSignature->sorts;s++){ 
    Stack<GroundedTerm> groundedTerms = _sortedGroundedTerms[s];
    for(unsigned i=0;i< groundedTerms.length();i++){
        GroundedTerm gt = groundedTerms[i];
        unsigned arity = env.signature->functionArity(gt.f);
        ASS(arity<2);
        static DArray<unsigned> grounding;
        grounding.ensure(arity+1);
        grounding[arity]=size;
        if(arity==0){
          satClauseLits.push(getSATLiteral(gt.f,grounding,true,true)); 
        }
        else{
          for(unsigned m=1;m<=size;m++){
            //assume arity=1
            grounding[0]=m;
            satClauseLits.push(getSATLiteral(gt.f,grounding,true,true)); 
          }
        }
    }
  }

  addSATClause(SATClause::fromStack(satClauseLits));
*/
}

void FiniteModelBuilder::addNewTotalityDefs()
{
  CALL("FiniteModelBuilder::addNewTotalityDefs");

  if (_xmass) {
    // make sure to solve the problem of some sorts not growing all the way to _sortModelSizes[srt], because of _sortedSignature->sortBounds[srt]
    for (unsigned i = 0; i < _distinctSortSizes.size(); i++) {
      // for every sort
      for (unsigned j = 0; j < _distinctSortSizes[i]-1; j++) {
        // for every domain size j have clause: not marker(j+1) | marker(j)
        // which says: "d > j+2" -> "d > j+1"
        static SATLiteralStack satClauseLits;
        satClauseLits.reset();
        satClauseLits.push(SATLiteral(marker_offsets[i]+j,1));
        satClauseLits.push(SATLiteral(marker_offsets[i]+j+1,0));
        SATClause* satCl = SATClause::fromStack(satClauseLits);
        addSATClause(satCl);
      }
    }
  }

  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;
    unsigned arity = env.signature->functionArity(f);

#if VTRACE_FMB
    cout << "Adding total defs for " << env.signature->functionName(f) << endl;
#endif

    const DArray<unsigned>& f_signature = _sortedSignature->functionSignatures[f];

    if(arity==0){
      unsigned srt = f_signature[0];
      unsigned dsrt = _sortedSignature->parents[srt];
      unsigned maxSize = min(_sortedSignature->sortBounds[srt],_sortModelSizes[srt]);

      // cout << "Totality for const " << f << " of sort " << srt << " and max size " << maxSize << endl;

      for (unsigned i = (!_xmass || (_sortedSignature->monotonicSorts[dsrt])) ? maxSize : 1; i <= maxSize; i++) { // just the weakest one, if monotonic
        static SATLiteralStack satClauseLits;
        satClauseLits.reset();

        for(unsigned constant=1;constant<=i;constant++){
          static DArray<unsigned> use(1);
          use[0]=constant;
          SATLiteral slit = getSATLiteral(f,use,true,true);
          satClauseLits.push(slit);
        }
        if (_xmass) {
          unsigned marker_idx = (i == maxSize) ? _distinctSortSizes[dsrt]-1 : i-1; // use the largest marker for the largest version even if it is smaller than _distinctSortSizes[dsrt]
          satClauseLits.push(SATLiteral(marker_offsets[dsrt] + marker_idx,1));
          ///cout << "out sort " << dsrt;
          // cout << "  version for size " << i << " marked with " << i-1 << " positive" << endl;
        } else {
          satClauseLits.push(SATLiteral(totalityMarker_offset+dsrt,0));
        }

        SATClause* satCl = SATClause::fromStack(satClauseLits);
        addSATClause(satCl);
      }

      continue;
    }

    static DArray<unsigned> maxVarSize;
    maxVarSize.ensure(arity);
    for(unsigned var=0;var<arity;var++){
      unsigned srt = f_signature[var]; 
      maxVarSize[var] = min(_sortedSignature->sortBounds[srt],_sortModelSizes[srt]);
    }
    unsigned retSrt = f_signature[arity];
    unsigned dRetSrt = _sortedSignature->parents[retSrt];
    unsigned maxRtSrtSize = min(_sortedSignature->sortBounds[retSrt],_sortModelSizes[retSrt]);

    static DArray<unsigned> grounding;
    grounding.ensure(arity);
    for(unsigned var=0;var<arity;var++){ grounding[var]=1; }
    grounding[arity-1]=0;

newTotalLabel:
      for(unsigned var=arity-1;var+1!=0;var--){

        if(grounding[var]==maxVarSize[var]){
          grounding[var]=1;
        }
        else{
          grounding[var]++;
          //cout << "Grounding: ";
          //for(unsigned j=0;j<grounding.size();j++) cout << grounding[j] << " ";
          //cout << endl;

          for (unsigned i = (!_xmass || (_sortedSignature->monotonicSorts[dRetSrt])) ? maxRtSrtSize : 1; i <= maxRtSrtSize; i++) {
            static SATLiteralStack satClauseLits;
            satClauseLits.reset();

            for(unsigned constant=1;constant<=i;constant++) {
              static DArray<unsigned> use;
              use.ensure(arity+1);
              for(unsigned k=0;k<arity;k++) use[k]=grounding[k];
              use[arity]=constant;
              satClauseLits.push(getSATLiteral(f,use,true,true));
            }
            if (_xmass) {
              unsigned marker_idx = (i == maxRtSrtSize) ? _distinctSortSizes[dRetSrt]-1 : i-1; // use the largest marker for the largest version even if it is smaller than _distinctSortSizes[dsrt]
              satClauseLits.push(SATLiteral(SATLiteral(marker_offsets[dRetSrt]+marker_idx,1)));
            } else {
              satClauseLits.push(SATLiteral(totalityMarker_offset+dRetSrt,0));
            }
            SATClause* satCl = SATClause::fromStack(satClauseLits);
            addSATClause(satCl);
          }
          goto newTotalLabel;
        }
      }
  }
}


/*
 * We expect grounding to have [x,y] for predicate p(x,y) and [x,y,z] for function z=f(x,y)
 * i.e. as noted above grounding[arity] should be the return for a function
 *
 */
SATLiteral FiniteModelBuilder::getSATLiteral(unsigned f, const DArray<unsigned>& grounding,
                                                           bool polarity,bool isFunction)
{
  CALL("FiniteModelBuilder::getSATLiteral");

  // cannot have predicate 0 here (it's equality)
  ASS(f>0 || isFunction);

  DEBUG_CODE(
    unsigned arity = isFunction ? env.signature->functionArity(f) : env.signature->predicateArity(f)
  );
  ASS((isFunction && arity==grounding.size()-1) || (!isFunction && arity==grounding.size()));

  unsigned offset = isFunction ? f_offsets[f] : p_offsets[f];

  //cout << "getSATLiteral " << f<< ","  << offset << ", grounding = ";
  //for(unsigned i=0;i<grounding.size();i++) cout <<  grounding[i] << " "; 
  //cout << endl;

  DArray<unsigned>& signature = isFunction ?
             _sortedSignature->functionSignatures[f] : 
             _sortedSignature->predicateSignatures[f];

  unsigned var = offset;
  unsigned mult=1;
  for(unsigned i=0;i<grounding.size();i++){
    var += mult*(grounding[i]-1);
    unsigned srt = signature[i];
    //cout << var << ", " << mult << "," << _sortModelSizes[srt] << endl;
    mult *= _sortModelSizes[srt];
  }
  //cout << "return " << var << endl;

  return SATLiteral(var,polarity);
}

void FiniteModelBuilder::addSATClause(SATClause* cl)
{
  CALL("FiniteModelBuilder::addSATClause");
  cl = SATClause::removeDuplicateLiterals(cl);
  if(!cl){ return; }
#if VTRACE_FMB
  cout << "ADDING " << cl->toString() << endl; // " of size " << cl->length() << endl;
#endif

  _clausesToBeAdded.push(cl);

}

MainLoopResult FiniteModelBuilder::runImpl()
{
  CALL("FiniteModelBuilder::runImpl");

  if(!_isAppropriate){
    // give up!
    return MainLoopResult(Statistics::INAPPROPRIATE);
  }
  if(!_prb.units()){
    return MainLoopResult(Statistics::SATISFIABLE);
  }

  env.statistics->phase = Statistics::FMB_CONSTRAINT_GEN;


  if(outputAllowed()){
      bool doPrinting = false;
#if VTRACE_FMB
      doPrinting = true;
#endif
      vstring res = "[";
      for(unsigned s=0;s<_sortedSignature->distinctSorts;s++){
        if(_distinctSortMaxs[s]==UINT_MAX){
          res+="max";
        }else{
          res+=Lib::Int::toString(_distinctSortMaxs[s]);
          doPrinting=true;
        }
        if(s+1 < _sortedSignature->distinctSorts) res+=",";
      }
      if(doPrinting){
        cout << "Detected maximum model sizes of " << res << "]" << endl;
      }
  }

  _sortModelSizes.ensure(_sortedSignature->sorts);
  _distinctSortSizes.ensure(_sortedSignature->distinctSorts);
  for(unsigned i=0;i<_distinctSortSizes.size();i++){
     _distinctSortSizes[i]=max(_startModelSize,_distinctSortMins[i]);
  }
  for(unsigned s=0;s<_sortedSignature->sorts;s++) {
    _sortModelSizes[s] = _distinctSortSizes[_sortedSignature->parents[s]];
  }

  if (!_xmass) {
    if (!_dsaEnumerator->init(_startModelSize,_distinctSortSizes,_distinct_sort_constraints,_strict_distinct_sort_constraints)) {
      goto gave_up;
    }
  }

  if (reset()) {
  while(true){
    if(outputAllowed()) {
      cout << "TRYING " << "["; 
      for(unsigned i=0;i<_distinctSortSizes.size();i++){
        cout << _distinctSortSizes[i];
        if(i+1 < _distinctSortSizes.size()) cout << ",";
      }
      cout << "]" << endl;
    }
    Timer::syncClock();
    if(env.timeLimitReached()){ return MainLoopResult(Statistics::TIME_LIMIT); }

    {
    TimeCounter tc(TC_FMB_CONSTRAINT_CREATION);

    // add the new clauses to _clausesToBeAdded
#if VTRACE_FMB
    cout << "GROUND" << endl;
#endif
    addGroundClauses();
#if VTRACE_FMB
    cout << "INSTANCES" << endl;
#endif
    addNewInstances();
#if VTRACE_FMB
    cout << "FUNC DEFS" << endl;
#endif
    addNewFunctionalDefs();
#if VTRACE_FMB
    cout << "SYM DEFS" << endl;
#endif
    addNewSymmetryAxioms();
    
#if VTRACE_FMB
    cout << "TOTAL DEFS" << endl;
#endif
    addNewTotalityDefs();

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

    SATSolver::Status satResult = SATSolver::UNKNOWN;
    {
      env.statistics->phase = Statistics::FMB_SOLVING;
      TimeCounter tc(TC_FMB_SAT_SOLVING);

      static SATLiteralStack assumptions(_distinctSortSizes.size());
      assumptions.reset();
      if (_xmass) {
        for (unsigned i = 0; i < _distinctSortSizes.size(); i++) {
          assumptions.push(SATLiteral(marker_offsets[i]+_distinctSortSizes[i]-1,0));
          // cout << "assuming sort " << i << " value " << _distinctSortSizes[i]-1 << " negative" << endl;
        }
      } else {
        for (unsigned i = 0; i < _distinctSortSizes.size(); i++) {
          assumptions.push(SATLiteral(totalityMarker_offset+i,1));
        }
        for (unsigned i = 0; i < _distinctSortSizes.size(); i++) {
          assumptions.push(SATLiteral(instancesMarker_offset+i,1));
        }
      }

      satResult = _solver->solveUnderAssumptions(assumptions);
      env.statistics->phase = Statistics::FMB_CONSTRAINT_GEN;
    }

    // if the clauses are satisfiable then we have found a finite model
    if(satResult == SATSolver::SATISFIABLE){
      onModelFound();
      return MainLoopResult(Statistics::SATISFIABLE);
    }

    static unsigned numberOfSatCalls = 0;
    numberOfSatCalls++;
    unsigned clauseSetSize = _clausesToBeAdded.size();
    unsigned weight = clauseSetSize;

    // destroy the clauses
    SATClauseStack::Iterator it(_clausesToBeAdded);
    while (it.hasNext()) {
      it.next()->destroy();
    }
    // but the container needs to be empty for the next round in any case
    _clausesToBeAdded.reset();

    {
      // _solver->explicitlyMinimizedFailedAssumptions(false,true); // TODO: try adding this in
      const SATLiteralStack& failed = _solver->failedAssumptions();

      if (_xmass) {
        unsigned domToGrow = UINT_MAX;
        unsigned domsWeight = UINT_MAX;

        static unsigned alternator = 0;
        alternator++;

        for (unsigned i = 0; i < failed.size(); i++) {
          unsigned var = failed[i].var();

          unsigned srt = which_sort(var);

          // cout << "which_sort(var) = " << srt << endl;

          // skip if already maxed
          if (_distinctSortSizes[srt] == _distinctSortMaxs[srt]) {
            continue;
          }

          unsigned weight = 0;

          if (alternator % (_sizeWeightRatio+1) != 0) {
            _distinctSortSizes[srt]++;
            weight = estimateInstanceCount();
            _distinctSortSizes[srt]--;
          } else {
            weight = _distinctSortSizes[srt];
          }

  #if VTRACE_DOMAINS
          cout << "dom "<<srt<<" of weight "<< weight << " could grow." << endl;
  #endif
          if (weight < domsWeight) {
            domToGrow = srt;
            domsWeight = weight;
          }
        }

        if (domsWeight < UINT_MAX) {
          ASS_L(domToGrow,UINT_MAX);
  #if VTRACE_DOMAINS
          cout << "chosen "<<domToGrow<< " of weight " << domsWeight << endl;
  #endif
          _distinctSortSizes[domToGrow]++;

          { // check distinct sort constraints (until fixpoint)
            bool updated;
            do {
              updated = false;
              Stack<std::pair<unsigned,unsigned>>::Iterator it1(_distinct_sort_constraints);
              while (it1.hasNext()) {
                std::pair<unsigned,unsigned> constr = it1.next();
                if (_distinctSortSizes[constr.first] < _distinctSortSizes[constr.second]) {
                  _distinctSortSizes[constr.first] = _distinctSortSizes[constr.second];
                  updated = true;
                }
              }

              Stack<std::pair<unsigned,unsigned>>::Iterator it2(_strict_distinct_sort_constraints);
              while (it1.hasNext()) {
                std::pair<unsigned,unsigned> constr = it1.next();
                if (_distinctSortSizes[constr.first] <= _distinctSortSizes[constr.second]) {
                  _distinctSortSizes[constr.first] = _distinctSortSizes[constr.second]+1;
                  updated = true;
                }
              }

            } while (updated);
          }

          for(unsigned s=0;s<_sortedSignature->sorts;s++) {
            _sortModelSizes[s] = _distinctSortSizes[_sortedSignature->parents[s]];
          }
        } else {
          Clause* empty = new(0) Clause(0,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::MODEL_NOT_FOUND));
          return MainLoopResult(Statistics::REFUTATION,empty);
        }
      } else { // i.e. (!_xmass)
        static Constraint_Generator_Vals nogood;

        nogood.ensure(_distinctSortSizes.size());

        for (unsigned i = 0; i < _distinctSortSizes.size(); i++) {
          nogood[i] = make_pair(STAR,_distinctSortSizes[i]);
        }

        for (unsigned i = 0; i < failed.size(); i++) {
          unsigned var = failed[i].var();
          ASS_GE(var,totalityMarker_offset);

          if (var < instancesMarker_offset) { // totality used (-> instances used as well / unless the sort is monotonic)
            unsigned dsort = var-totalityMarker_offset;
            if (_sortedSignature->monotonicSorts[dsort]) {
              nogood[dsort].first = LEQ;
            } else {
              nogood[dsort].first = EQ;
            }
          } else if (nogood[var-instancesMarker_offset].first == STAR) { // instances used (and we don't know yet about totality)
            ASS(!_sortedSignature->monotonicSorts[var-instancesMarker_offset]);
            nogood[var-instancesMarker_offset].first = GEQ;
          }
        }

#if VTRACE_DOMAINS
        cout << "Learned a nogood: ";
        output_cg(nogood);
        cout << " of weight " << weight << endl;
#endif

        _dsaEnumerator->learnNogood(nogood,weight);

        if (!_dsaEnumerator->increaseModelSizes(_distinctSortSizes,_distinctSortMaxs)) {
          if (_dsaEnumerator->isFmbComplete(_distinctSortSizes.size())) {
            Clause* empty = new(0) Clause(0,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::MODEL_NOT_FOUND));
            return MainLoopResult(Statistics::REFUTATION,empty);
          } else {
            if(outputAllowed()) {
              cout << "Cannot enumerate next child to try in an incomplete setup" <<endl;
            }
            goto gave_up;
          }
        }

        for(unsigned s=0;s<_sortedSignature->sorts;s++) {
          _sortModelSizes[s] = _distinctSortSizes[_sortedSignature->parents[s]];
        }
      }
    }

    if(!reset()){
      break;
    }
  }
  }

  // reset returned false, we can't represent all the variables; giving up!

  if(outputAllowed()){
    cout << "Cannot represent all propositional literals internally" <<endl;
  }

  gave_up: // for jumping because of other reasons to give up (message printed elsewhere)

  /*
  // Giles: In CASC mode we should only print GaveUp at the very end
  if(UIHelper::szsOutput) {
    env.beginOutput();
    env.out() << "% SZS status GaveUp for " << _opt.problemName() << endl;
    env.endOutput();
  }
  */

  return MainLoopResult(Statistics::REFUTATION_NOT_FOUND);
}

void FiniteModelBuilder::onModelFound()
{
 CALL("FiniteModelBuilder::onModelFound");
 // Don't do any output if proof is off
 if(_opt.proof()==Options::Proof::OFF){ 
   return; 
 }

 reportSpiderStatus('-');
 if(outputAllowed()){
   cout << "Finite Model Found!" << endl;
 }

 //we need to print this early because model generating can take some time
 if(szsOutputMode()) {
   env.beginOutput();
   env.out() << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
       << " for " << _opt.problemName() << endl << flush;
   env.endOutput();
   UIHelper::satisfiableStatusWasAlreadyOutput = true;
 }
  // Prevent timing out whilst the model is being printed
  Timer::setLimitEnforcement(false);


 DHMap<unsigned,unsigned> vampireSortSizes;
 for(unsigned vSort=0;vSort<env.signature->typeCons();vSort++){
   unsigned size = 1;
   if(env.signature->isInterpretedNonDefault(vSort) && !env.signature->isBoolCon(vSort)){ size=0;}
   unsigned dsort;
   if(_sortedSignature->vampireToDistinctParent.find(vSort,dsort)){
     size = _distinctSortSizes[dsort];
   }
   vampireSortSizes.insert(vSort,size);
 }

  FiniteModelMultiSorted model(vampireSortSizes);

  //Record interpretation of constants
  for(unsigned f=0;f<env.signature->functions();f++){
    if(env.signature->functionArity(f)>0) continue;
    if(del_f[f]) continue;

    bool found=false;
    for(unsigned c=1;c<=_sortModelSizes[_sortedSignature->functionSignatures[f][0]];c++){
      static DArray<unsigned> grounding(1);
      grounding[0]=c;
      SATLiteral slit = getSATLiteral(f,grounding,true,true);
      if(_solver->trueInAssignment(slit)){
        //if(found){ cout << "Error: multiple interpretations of " << name << endl;}
        ASS(!found);
        found=true;
        model.addConstantDefinition(f,c);
      }
    }
    ASS(found);
  }

  //Record interpretation of functions 
  for(unsigned f=0;f<env.signature->functions();f++){
    unsigned arity = env.signature->functionArity(f);
    if(arity==0) continue;
    if(del_f[f]) continue;

    //cout << "For " << env.signature->getFunction(f)->name() << endl;

    static DArray<unsigned> grounding;
    grounding.ensure(arity);
    for(unsigned i=0;i<arity;i++){
       grounding[i]=1;
    }
    grounding[arity-1]=0;

    const DArray<unsigned>& f_signature = _sortedSignature->functionSignatures[f];
    static DArray<unsigned> maxVarSize;
    maxVarSize.ensure(arity);
    for(unsigned var=0;var<arity;var++){ 
      unsigned srt = f_signature[var];
      maxVarSize[var] = min(_sortedSignature->sortBounds[srt],_sortModelSizes[srt]);
    }
    unsigned retSrt = f_signature[arity];
    unsigned maxRtSrtSize = min(_sortedSignature->sortBounds[retSrt],_sortModelSizes[retSrt]);

fModelLabel:
      for(unsigned var=arity-1;var+1!=0;var--){

        if(grounding[var] == maxVarSize[var]){
          grounding[var]=1;
        }
        else{
          grounding[var]++;

          static DArray<unsigned> use;
          use.ensure(arity+1);
          for(unsigned k=0;k<arity;k++) use[k]=grounding[k];

          bool found=false;
          for(unsigned c=1;c<=maxRtSrtSize;c++){
            use[arity]=c;
            SATLiteral slit = getSATLiteral(f,use,true,true);
            if(_solver->trueInAssignment(slit)){
              //if(found){ cout << "Error: multiple interpretations of " << name << endl; }
              ASS(!found);
              found=true;
              model.addFunctionDefinition(f,grounding,c);
            }
          }
          if(!found){
             // This means that there is no result for this input
             // This is a result of the finite sort bounding and the argument
             // says that we can equate this domain element to a smaller one below the bound
             //TODO fix this 
             //cout << "NOT FOUND for " << env.signature->functionName(f) << endl; 
          }

          goto fModelLabel;
        }
      }
  }


  //Record interpretation of prop symbols 
  static const DArray<unsigned> emptyG(0);
  for(unsigned f=1;f<env.signature->predicates();f++){
    if(env.signature->predicateArity(f)>0) continue;
    if(del_p[f]) continue;
    if(_partiallyDeletedPredicates.find(f)) continue;

    bool res;
    if(!_trivialPredicates.find(f,res)){ 
      SATLiteral slit = getSATLiteral(f,emptyG,true,false);
      res=_solver->trueInAssignment(slit); 
    }
    model.addPropositionalDefinition(f,res);
  }

  //Record interpretation of predicates 
  for(unsigned f=1;f<env.signature->predicates();f++){
    unsigned arity = env.signature->predicateArity(f);
    if(arity==0) continue;
    if(del_p[f]) continue;
    if(_partiallyDeletedPredicates.find(f)) continue;

    //cout << "Record for " << env.signature->getPredicate(f)->name() << endl;

    static DArray<unsigned> grounding;
    static DArray<unsigned> args;
    grounding.ensure(arity);
    args.ensure(arity);
    for(unsigned i=0;i<arity-1;i++){grounding[i]=1;args[1]=1;}
    grounding[arity-1]=0;
    args[arity-1]=0;

    const DArray<unsigned>& f_signature = _sortedSignature->predicateSignatures[f];
    static DArray<unsigned> maxVarSize;
    maxVarSize.ensure(arity);
    for(unsigned var=0;var<arity;var++){
      unsigned srt = f_signature[var];
      maxVarSize[var] = _sortedSignature->sortBounds[srt];
    }

pModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){
    
        if(args[i]==_sortModelSizes[f_signature[i]]){
          grounding[i]=1;
          args[i]=1;
       }
        else{
          if(args[i]<maxVarSize[i]){
            grounding[i]++;
          }
          args[i]++;
          bool res;
          if(!_trivialPredicates.find(f,res)){ 
            SATLiteral slit = getSATLiteral(f,grounding,true,false);
            res=_solver->trueInAssignment(slit); 
          }
          //for(unsigned j=0;j<arity;j++){ cout << grounding[j] << ", ";}; cout << " = " << res << endl;

          model.addPredicateDefinition(f,grounding,res);

          goto pModelLabel;
        }
      }
  }


  //Evaluate removed functions and constants
  unsigned maxf = env.signature->functions(); // model evaluation can add new constants
  //bool unfinished=true;
  //while(unfinished){
  //unfinished=false;
  unsigned f=maxf;
  while(f > 0){ 
    f--;
    //cout << "Consider " << f << endl;
    unsigned arity = env.signature->functionArity(f);
    if(!del_f[f]) continue; 
    // For now, just skip unused functions!
    if(env.signature->getFunction(f)->usageCnt()==0) continue;
    //del_f[f]=false;

    ASS(_deletedFunctions.find(f));
    Literal* def = _deletedFunctions.get(f);

    //cout << "For " << env.signature->getFunction(f)->name() << endl;
    //cout << def->toString() << endl;

    ASS(def->isEquality());
    Term* funApp = 0; 
    Term* funDef = 0;

    if(def->nthArgument(0)->term()->functor()==f){
      funApp = def->nthArgument(0)->term();
      funDef = def->nthArgument(1)->term();
    }
    else{
      ASS(def->nthArgument(1)->term()->functor()==f);
      funApp = def->nthArgument(1)->term();
      funDef = def->nthArgument(0)->term();
    }

    ASS(def->polarity());
    DArray<int> vars(arity);
    for(unsigned i=0;i<arity;i++){
      ASS(funApp->nthArgument(i)->isVar());
      vars[i] = funApp->nthArgument(i)->var();
    }

    if(arity>0){
      static DArray<unsigned> grounding;
      static DArray<unsigned> f_signature_distinct(arity);
      grounding.ensure(arity);
      f_signature_distinct.ensure(arity);
      for(unsigned i=0;i<arity-1;i++){
        grounding[i]=1;
        TermList vs = env.signature->getFunction(f)->fnType()->arg(i);
        unsigned vampireSrt = vs.term()->functor();
        ASS(_sortedSignature->vampireToDistinctParent.find(vampireSrt));
        unsigned dsrt = _sortedSignature->vampireToDistinctParent.get(vampireSrt);
        f_signature_distinct[i] = dsrt;
      }
      grounding[arity-1]=0;

      const DArray<unsigned> f_signature(arity);

ffModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(grounding[i]==_distinctSortSizes[f_signature_distinct[i]]){
          grounding[i]=1;
        }
        else{
          grounding[i]++;

          Substitution subst;
          for(unsigned j=0;j<arity;j++){
            TermList vs = env.signature->getFunction(f)->fnType()->arg(j); 
            unsigned vampireSrt = vs.term()->functor();
            //cout << grounding[j] << " is " << model.getDomainConstant(grounding[j],vampireSrt)->toString() << endl;
            subst.bind(vars[j],model.getDomainConstant(grounding[j],vampireSrt));
          }
          Term* defGround = SubstHelper::apply(funDef,subst);
          //cout << predDefGround << endl;
          try{
            unsigned res = model.evaluateGroundTerm(defGround);
            model.addFunctionDefinition(f,grounding,res);
          }
          catch(UserErrorException& exception){
            //cout << "Setting unfinished" << endl;
            //unfinished=true;
            //del_f[f]=true;
          }

          goto ffModelLabel;
        }
      }
    }
    else{
      //constant
      try{
        model.addConstantDefinition(f,model.evaluateGroundTerm(funDef));
      }
      catch(UserErrorException& exception){
        //cout << "Setting unfinished" << endl;
        //unfinished=true;  
        //del_f[f]=true;
      }
    }
  }
  //}

  //Evaluate removed propositions and predicates
  f=env.signature->predicates()-1;
  while(f>0){
    f--;
    if(!del_p[f] && !_partiallyDeletedPredicates.find(f)) continue;
    if(_trivialPredicates.find(f)) continue;
    unsigned arity = env.signature->predicateArity(f);

    ASS(!del_p[f] || _deletedPredicates.find(f));
    ASS(del_p[f] || _partiallyDeletedPredicates.find(f));
    Unit* udef = del_p[f] ? _deletedPredicates.get(f) : _partiallyDeletedPredicates.get(f);

    //if(_partiallyDeletedPredicates.find(f)){
      //cout << "For " << env.signature->getPredicate(f)->name() << endl;
      //cout << udef->toString() << endl;
    //}
    Formula* def = udef->getFormula();   
    Literal* predApp = 0;
    Formula* predDef = 0;
    bool polarity = true;
    bool pure = false;

    switch(def->connective()){
      case FORALL:
      {
        Formula* inner = def->qarg();
        ASS(inner->connective()==Connective::IFF);
        Formula* left = inner->left();
        Formula* right = inner->right(); 

        if(left->connective()==Connective::NOT){
          polarity=!polarity;
          left = left->uarg();
        }
        if(right->connective()==Connective::NOT){
          polarity=!polarity;
          right = right->uarg();
        }

        if(left->connective()==Connective::LITERAL){
          if(left->literal()->functor()==f){
            predDef = right;
            predApp = left->literal();
          }
        }
        if(!predDef){
          ASS(right->connective()==Connective::LITERAL);
          ASS(right->literal()->functor()==f);
          predDef = left;
          predApp = right->literal();
        }
        break;
      }
      case TRUE:
        pure=true;
        polarity=true;
        break;
      case FALSE:
        pure=true;
        polarity=false;
        break;
      default: ASSERTION_VIOLATION;
    }

    ASS(pure || (predDef && predApp));
    if(!pure && (!predDef || !predApp)) continue; // we failed, ignore this

    DArray<int> vars(arity);
    if(!pure){
      if(!predApp->polarity()) polarity=!polarity;
      for(unsigned i=0;i<arity;i++){
        ASS(predApp->nthArgument(i)->isVar());
        vars[i] = predApp->nthArgument(i)->var();
      }
    }

    static DArray<unsigned> grounding;
    static DArray<unsigned> p_signature_distinct;
    grounding.ensure(arity);
    p_signature_distinct.ensure(arity);
    for(unsigned i=0;i<arity;i++){
      grounding[i]=1;
      TermList vs = env.signature->getPredicate(f)->predType()->arg(i);
      unsigned vampireSrt = vs.term()->functor();
      unsigned dsrt = _sortedSignature->vampireToDistinctParent.get(vampireSrt); 
      p_signature_distinct[i] = dsrt;
    }
    grounding[arity-1]=0;


ppModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(grounding[i]==_distinctSortSizes[p_signature_distinct[i]]){
          grounding[i]=1;
        }
        else{
          grounding[i]++;

          if(pure){
            model.addPredicateDefinition(f,grounding,polarity);
          }
          else{
            Substitution subst;
            for(unsigned j=0;j<arity;j++){ 
              //cout << grounding[j] << " is " << model.getDomainConstant(grounding[j])->toString() << endl;
              TermList vs = env.signature->getPredicate(f)->predType()->arg(j); 
              unsigned vampireSrt = vs.term()->functor();
              subst.bind(vars[j],model.getDomainConstant(grounding[j],vampireSrt));
            }
            Formula* predDefGround = SubstHelper::apply(predDef,subst);
            //cout << predDefGround << endl;
            try{
              bool res = model.evaluate(
                new FormulaUnit(predDefGround, NonspecificInference0(UnitInputType::AXIOM, InferenceRule::INPUT)));
              if(!polarity) res=!res;
              model.addPredicateDefinition(f,grounding,res);
            }
            catch(UserErrorException& exception){ 
              // TODO order symbols for partial evaluation
            }
          }

          goto ppModelLabel;
        }
      }
  }

  env.statistics->model = model.toString();
}

void FiniteModelBuilder::HackyDSAE::learnNogood(Constraint_Generator_Vals& nogood, unsigned weight)
{
  CALL("FiniteModelBuilder::HackyDSAE::learnNogood");

  Constraint_Generator* constraint_p = new Constraint_Generator(nogood,weight);

  _constraints_generators.insert(constraint_p);

  if (weight > _maxWeightSoFar) {
    _maxWeightSoFar = weight;
  }
}

bool FiniteModelBuilder::HackyDSAE::checkConstriant(DArray<unsigned>& newSortSizes, Constraint_Generator_Vals& constraint)
{
  CALL("FiniteModelBuilder::HackyDSAE::checkConstriant");

  for (unsigned j = 0; j < newSortSizes.size(); j++) {
    pair<ConstraintSign,unsigned>& cc = constraint[j];
    if (cc.first == EQ && cc.second != newSortSizes[j]) {
      return false;
    }
    if (cc.first == GEQ && cc.second > newSortSizes[j]) {
      return false;
    }
    if (cc.first == LEQ && cc.second < newSortSizes[j]) {
      return false;
    }
  }

#if VTRACE_DOMAINS
  cout << "  Ruled out by "; output_cg(constraint); cout << endl;
#endif

  return true;
}

bool FiniteModelBuilder::HackyDSAE::increaseModelSizes(DArray<unsigned>& newSortSizes, DArray<unsigned>& sortMaxes)
{
  CALL("FiniteModelBuilder::HackyDSAE::increaseModelSizes");

  // cout << "_constraints_generators.size() " << _constraints_generators.size() << endl;

  while (!_constraints_generators.isEmpty()) {
    Constraint_Generator* generator_p = _constraints_generators.top();
    Constraint_Generator_Vals& generator = generator_p->_vals;

#if VTRACE_DOMAINS
    cout << "Picking generator: ";
    FiniteModelBuilder::output_cg(generator);
    cout << endl;
#endif

    // copy generator to _distinctSortSizes
    for (unsigned i = 0; i< newSortSizes.size(); i++) {
      newSortSizes[i] = generator[i].second;
    }

    // all possible increments [+1,+0,+0,..],[+0,+1,+0,..],[+0,+0,+1,..], ...
    for (unsigned i = 0; i< newSortSizes.size(); i++) {
      // generate
      newSortSizes[i] += 1;

      // test 1 -- max sizes
      if (newSortSizes[i] > sortMaxes[i]) {
        //cout << "Skipping increasing distinct sort " << i << " as has max of " << _distinctSortMaxs[i] << endl;
        goto next_candidate;
      }

#if VTRACE_DOMAINS
      cout << "  Testing increment on " << i << endl;
#endif

      // test 2a -- generator constraints
      {
        Constraint_Generator_Heap::Iterator it(_constraints_generators);
        while (it.hasNext()) {
          if (checkConstriant(newSortSizes,it.next()->_vals)) {
            goto next_candidate;
          }
        }
      }

      // test 2b -- old generators // keeping old generators degraded performance on average ...
      /*
      {
        for (unsigned n = 0; n < _old_generators.size(); n++) {
          if (checkConstriant(newSortSizes,_old_generators[n]->_vals)) {

            // to stay "more complete", we generate the child anyway

            Constraint_Generator* gen_p = new Constraint_Generator(newSortSizes.size(), ++_maxWeightSoFar);
            Constraint_Generator_Vals& gen = gen_p->_vals;
            for (unsigned j = 0; j < newSortSizes.size(); j++) {
              gen[j] = make_pair(EQ,newSortSizes[j]);
            }

            _constraints_generators.insert(gen_p);

            goto next_candidate;
          }
        }
      }
      */

      // test 3 -- (strict)_distinct_sort_constraints
      {
        Stack<std::pair<unsigned,unsigned>>::Iterator it1(*_distinct_sort_constraints);
        while (it1.hasNext()) {
          std::pair<unsigned,unsigned> constr = it1.next();
          if (newSortSizes[constr.first] < newSortSizes[constr.second]) {
  #if VTRACE_DOMAINS
             cout << "  Ruled out by _distinct_sort_constraints " << constr.first << " >= " << constr.second << endl;
  #endif

            // We will skip testing it, but we need it as a generator to proceed through the space:
            Constraint_Generator* gen_p = new Constraint_Generator(newSortSizes.size(), ++_maxWeightSoFar /*effectively a fallback to FIFO for artificial children*/);
            Constraint_Generator_Vals& gen = gen_p->_vals;
            for (unsigned j = 0; j < newSortSizes.size(); j++) {
              gen[j] = make_pair(STAR,newSortSizes[j]);
            }
            gen[constr.first].first = EQ;
            gen[constr.second].first = GEQ;

            _constraints_generators.insert(gen_p);

            goto next_candidate;
          }
        }

        Stack<std::pair<unsigned,unsigned>>::Iterator it2(*_strict_distinct_sort_constraints);
        while (it2.hasNext()) {
          std::pair<unsigned,unsigned> constr = it2.next();
          if (newSortSizes[constr.first] <= newSortSizes[constr.second]) {
            // cout << "  Ruled out by _strict_distinct_sort_constraints " << constr.first << " > " << constr.second << endl;

            // We will skip testing it, but we need it as a generator to proceed through the space:
            Constraint_Generator* gen_p = new Constraint_Generator(newSortSizes.size(), ++_maxWeightSoFar /*effectively a fallback to FIFO for artificial children*/);
            Constraint_Generator_Vals& gen = gen_p->_vals;
            for (unsigned j = 0; j < newSortSizes.size(); j++) {
              gen[j] = make_pair(STAR,newSortSizes[j]);
            }
            gen[constr.first].first = EQ;
            gen[constr.second].first = GEQ;

            _constraints_generators.insert(gen_p);

            goto next_candidate;
          }
        }
      }

      // all passed
      return true;

      //undo
      next_candidate:
      newSortSizes[i] -= 1;
    }

    delete _constraints_generators.pop();
    // _old_generators.push(_constraints_generators.pop()); // keeping old generators degraded performance on average ...
#if VTRACE_DOMAINS
    cout << "Deleted" << endl;
#endif
  }

  return false;
}


#if VZ3
bool FiniteModelBuilder::SmtBasedDSAE::init(unsigned _startModelSize, DArray<unsigned>& _distinctSortSizes,
      Stack<std::pair<unsigned,unsigned>>& _distinct_sort_constraints, Stack<std::pair<unsigned,unsigned>>& _strict_distinct_sort_constraints)
{
  CALL("FiniteModelBuilder::SmtBasedDSAE::init");

  _skippedSomeSizes = (_startModelSize > 1);

  BYPASSING_ALLOCATOR;

  try {
    // initialize the smt solver
    z3::expr zero = _context.int_val(_startModelSize-1);

    _sizeConstants.ensure(_distinctSortSizes.size());
    // _distinctSortSizes.size() - many int variables
    for(unsigned i=0;i<_sizeConstants.size();i++) {
      _sizeConstants[i] = new z3::expr(_context);
      *_sizeConstants[i] = _context.int_const((vstring("s")+Int::toString(i)).c_str());

      // asserted to be greater than zero
      _smtSolver.add(*_sizeConstants[i] > zero);
    }

    _lastWeight = _distinctSortSizes.size()*_startModelSize;

    // also add (_strict)_distinct_sort_constraints
    Stack<std::pair<unsigned,unsigned>>::Iterator it1(_distinct_sort_constraints);
    while (it1.hasNext()) {
      std::pair<unsigned,unsigned> constr = it1.next();
      _smtSolver.add(*_sizeConstants[constr.first] >= *_sizeConstants[constr.second]);
    }

    Stack<std::pair<unsigned,unsigned>>::Iterator it2(_strict_distinct_sort_constraints);
    while (it2.hasNext()) {
      std::pair<unsigned,unsigned> constr = it2.next();
      _smtSolver.add(*_sizeConstants[constr.first] > *_sizeConstants[constr.second]);
    }

    // if UNSAT now, we know this is "infinox-gaveup"
    if (_strict_distinct_sort_constraints.size() > 0) {
      if (_smtSolver.check() == z3::check_result::unsat) {
       if(outputAllowed()){
          cout << "Problem does not have a finite model." <<endl;
        }
        return false;
      }
    }
  } catch (std::bad_alloc& _) {
    reportZ3OutOfMemory();
  }

  return true;
}

void FiniteModelBuilder::SmtBasedDSAE::learnNogood(Constraint_Generator_Vals& nogood, unsigned weight)
{
  CALL("FiniteModelBuilder::SmtBasedDSAE::learnNogood");

  BYPASSING_ALLOCATOR;

  try {
    z3::expr z3clause = _context.bool_val(false);
    // turning a no-good into a clause
    for (unsigned i = 0; i < nogood.size(); i++) {
      switch(nogood[i].first) {
        case EQ:
          z3clause = z3clause || (*_sizeConstants[i] != _context.int_val(nogood[i].second));
          break;
        case LEQ:
          z3clause = z3clause || (*_sizeConstants[i] > _context.int_val(nogood[i].second));
          break;
        case GEQ:
          z3clause = z3clause || (*_sizeConstants[i] < _context.int_val(nogood[i].second));
          break;
        default:
          // pass
          ;
      }
    }
    _smtSolver.add(z3clause);

  } catch (std::bad_alloc& _) {
    reportZ3OutOfMemory();
  }
}

/** Assuming _smtSolver just returned SAT,
 *  load the values to szs
 *  and return the weight of the vector */
unsigned FiniteModelBuilder::SmtBasedDSAE::loadSizesFromSmt(DArray<unsigned>& szs)
{
  CALL("FiniteModelBuilder::SmtBasedDSAE::loadSizesFromSmt");
  unsigned weight = 0;

  z3::model model = _smtSolver.get_model();

  for (unsigned i = 0; i < szs.size(); i++) {
    int val;
    Z3_get_numeral_int(_context,model.eval(*_sizeConstants[i]),&val);
    szs[i] = (unsigned)val;
    weight += val;
  }

  return weight;
}

void FiniteModelBuilder::SmtBasedDSAE::reportZ3OutOfMemory()
{
  CALL("FiniteModelBuilder::SmtBasedDSAE::reportZ3OutOfMemory");

  env.beginOutput();
  reportSpiderStatus('m');
  env.out() << "Z3 ran out of memory" << endl;
  if(env.statistics) {
    env.statistics->print(env.out());
  }
#if VDEBUG
  Debug::Tracer::printStack(env.out());
#endif
  env.endOutput();
  System::terminateImmediately(1);
}

bool FiniteModelBuilder::SmtBasedDSAE::increaseModelSizes(DArray<unsigned>& newSortSizes, DArray<unsigned>& sortMaxes)
{
  CALL("FiniteModelBuilder::SmtBasedDSAE::increaseModelSizes");

  BYPASSING_ALLOCATOR;

  try {
    TimeCounter tc(TC_Z3_IN_FMB);

    z3::check_result result = _smtSolver.check();

    if (result == z3::check_result::unsat) {
      return false;
    }

    ASS_EQ(result,z3::check_result::sat); // could we get unknown from this simple fragment?

    unsigned weight = loadSizesFromSmt(newSortSizes);

    // TODO: for completeness, we don't need to minimize every time round (which might be a bit expensive)

    if (weight == _lastWeight) {
      // cout << "Found "; output_sizes(_distinctSortSizes); cout << " of optimal weight " << weight;
      return true;
    }

    // TODO: try a more clever "fitness" than the sum; then minimizing by "halving" could be an interesting thing to try

    //cout << "Minimizing for weight ";

    // minimizing:
    while (true) {
      // cout << _lastWeight << ", ";

      _smtSolver.push();

      z3::expr sum = _context.int_val(0);
      for (unsigned i = 0; i < newSortSizes.size(); i++) {
        sum = sum + *_sizeConstants[i];
      }
      _smtSolver.add(sum == _context.int_val(_lastWeight));

      if (_smtSolver.check() == z3::check_result::sat) {
        loadSizesFromSmt(newSortSizes);
        // cout << "\nFound "; output_sizes(_distinctSortSizes); cout << endl;
        _smtSolver.pop(1);
        return true;
      } else {
        _smtSolver.pop(1);
        _lastWeight++;
      }
    }

  } catch (std::bad_alloc& _) {
    reportZ3OutOfMemory();
  }
  return true; // just to silence the compiler
}

#endif

}
