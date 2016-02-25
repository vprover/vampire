/**
 * @file FiniteModelBuilder.cpp
 * Implements class FiniteModelBuilder.
 */

#include <math.h>

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

#include "SAT/Preprocess.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/LingelingInterfacing.hpp"
#include "SAT/MinisatInterfacingNewSimp.hpp"
#include "SAT/BufferedSolver.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"
#include "Lib/Sort.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/GeneralSplitting.hpp"

#include "DP/DecisionProcedure.hpp"
#include "DP/SimpleCongruenceClosure.hpp"

#include "FiniteModel.hpp"
#include "ClauseFlattening.hpp"
#include "SortInference.hpp"
#include "DefinitionIntroduction.hpp"
#include "FiniteModelBuilder.hpp"

#define VTRACE_FMB 0

namespace FMB 
{

FiniteModelBuilder::FiniteModelBuilder(Problem& prb, const Options& opt)
: MainLoop(prb, opt), _sortedSignature(0), _groundClauses(0),_clauses(0),
                      _isComplete(true), _maxModelSize(UINT_MAX), _constantCount(0),
                      _maxArity(0)
{
  CALL("FiniteModelBuilder::FiniteModelBuilder");

  // If we are incomplete then stop now
  // Can be incomplete if we used incomplete version of equality proxy
  if(!opt.complete(prb)){
    _isComplete = false;
    return;
  }
  // Record option values
  _startModelSize = opt.fmbStartSize();
  _useConstantsAsStart = opt.fmbStartWithConstants();
  _symmetryRatio = opt.fmbSymmetryRatio();

  // Load any symbols removed during preprocessing (and their definitions)
  _deletedFunctions.loadFromMap(prb.getEliminatedFunctions());
  _deletedPredicates.loadFromMap(prb.getEliminatedPredicates());
  _partiallyDeletedPredicates.loadFromMap(prb.getPartiallyEliminatedPredicates());
  _trivialPredicates.loadFromMap(prb.trivialPredicates());

  // Record the maximum arity of a function
  _maxArity = 0;
  for(unsigned f=0;f<env.signature->functions();f++){
    unsigned arity = env.signature->functionArity(f);
    if(arity>_maxArity) _maxArity = arity;
  }

}


// Do all setting up required for finite model search for model of size size
// Returns false we if we failed to reset, this can happen if offsets overflow 2^32, possible for
// large signatures and large models. If this a frequent problem then we can go to longs.
bool FiniteModelBuilder::reset(unsigned size){
  CALL("FiniteModelBuilder::reset");

  // Construct the offsets for symbols
  // Each symbol requires size^(n+1) variables where n is the number of spaces for grounding
  // For function symbols we have n=arity+1 as we have the return value
  // For predicate symbols n=arity 

  static const unsigned VAR_MAX = MinisatInterfacingNewSimp::VAR_MAX;

  // Start from 1 as SAT solver variables are 1-based
  unsigned offsets=1;
  for(unsigned f=0; f<env.signature->functions();f++){
    if(del_f[f]) continue; 
    unsigned arity=env.signature->functionArity(f);
    //cout << f << "("<<arity<<") has " << offsets << endl;
    f_offsets[f]=offsets;
    unsigned add = pow(size,arity+2);
    // Check that we do not overflow
    if(VAR_MAX - add < offsets){
      return false;
    }
    offsets += add;
  }
  // Start from p=1 as we ignore equality
  for(unsigned p=1; p<env.signature->predicates();p++){
    if(del_p[p]) continue;
    unsigned arity=env.signature->predicateArity(p);
    //cout << p << "("<<arity<<") has " << offsets << endl;
    p_offsets[p]=offsets;
    unsigned add = pow(size,arity+1);
    // Check for overflow
    if(VAR_MAX - add < offsets){
      return false;
    }
    offsets += add; 
  }

  // Create a new SAT solver
  switch(_opt.satSolver()){
    case Options::SatSolver::VAMPIRE:
      _solver = new TWLSolver(_opt, true);
      break;
    case Options::SatSolver::LINGELING:
      _solver = new LingelingInterfacing(_opt, true);
      break;
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

  // set the number of SAT variables, this could cause an exception
  _solver->ensureVarCount(offsets+1);

  // needs to be redone for each size as we use this to pick the number of
  // things to order and the constants to ground with 
  createSymmetryOrdering(size);

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

void FiniteModelBuilder::createSymmetryOrdering(unsigned size)
{
  CALL("FiniteModelBuilder::createSymmeteryOrdreing");
  
  // only really required the first time
  _sortedGroundedTerms.ensure(_sortedSignature->sorts);

  // Build up an ordering of GroundedTerms per sort
  for(unsigned s=0;s<_sortedSignature->sorts;s++){

    // Remove any previously computed ordering
    _sortedGroundedTerms[s].reset();

    // Add all the constants of that sort
    for(unsigned c=0;c<_sortedSignature->sortedConstants[s].length();c++){
      GroundedTerm g;
      g.f = _sortedSignature->sortedConstants[s][c];
      g.grounding = 0; // no grounding needed, use 0 as a place-holder
      _sortedGroundedTerms[s].push(g);
      //cout << "Adding " << g.f << "," << g.grounding << " to " << s << endl;
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
          if(_sortedSignature->functionBounds[g.f][0] < size) continue;

          g.grounding = m; 

          // We skip f if its domain is bounded to less than g.grounding
          bool outOfBounds = false;
          for(unsigned i=0;i<env.signature->functionArity(g.f);i++){
            if(_sortedSignature->functionBounds[g.f][i+1] < g.grounding)
              outOfBounds=true;
          }
          if(outOfBounds) continue;

          _sortedGroundedTerms[s].push(g);
          //cout << "Adding " << g.f << "," << g.grounding << " to " << s << endl;
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
          if(_sortedSignature->functionBounds[g.f][0] < size) continue;

          // If doing arg_first then we ignore the diagonal thing
          // otherwise the grounding is this weird function of m, f and size
          g.grounding = arg_first ? m : 1+((m+f)%(size));

          // We skip f if its domain is bounded to less than g.grounding
          bool outOfBounds = false;
          for(unsigned i=0;i<env.signature->functionArity(g.f);i++){
            if(_sortedSignature->functionBounds[g.f][i+1] < g.grounding)
              outOfBounds=true;
          }
          if(outOfBounds) continue;
  
          _sortedGroundedTerms[s].push(g);
          //cout << "Adding " << g.f << "," << g.grounding << " to " << s << endl;
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
  if(!_isComplete) return;

  env.statistics->phase = Statistics::FMB_PREPROCESSING;

/* For an ongoing experiment
  {
    //TODO consider ordering
    OrderingSP ordering = OrderingSP(Ordering::create(_prb, _opt));
    DP::SimpleCongruenceClosure* congruence = new DP::SimpleCongruenceClosure(*ordering);
    LiteralStack lstack;
    ClauseIterator cit = _prb.clauseIterator();
    while(cit.hasNext()){
      Clause* c = cit.next();
      if(c->size()==1){
        Literal* lit = (*c)[0];
        if(lit->ground()) lstack.push(lit);
      } 
    }
    congruence->addLiterals(pvi(LiteralStack::Iterator(lstack)),false);
    DP::DecisionProcedure::Status status = congruence->getStatus();
    if(status == DP::DecisionProcedure::SATISFIABLE){
	// check constants
	for(unsigned f=0;f<env.signature->functions();f++){
	  unsigned arity = env.signature->functionArity(f);
	  if(arity>0) continue;
	  Term* c = Term::createConstant(f);
	  unsigned cls = congruence->getClassID(TermList(c));
	  cout << f << ": " << cls << endl;
	}
    } 
    if(status == DP::DecisionProcedure::UNKNOWN) USER_ERROR("UNKNOWN");
    USER_ERROR("UNSAT");
  }
*/

  // Perform DefinitionIntroduction as we iterate
  // over the clauses of the problem
  DefinitionIntroduction cit = DefinitionIntroduction(_prb.clauseIterator());
  //ClauseIterator cit = _prb.clauseIterator();

  // Apply flattening and split clauses into ground and non-ground
  while(cit.hasNext()){
    Clause* c = cit.next();
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
      _groundClauses = _groundClauses->cons(c);
    }else{
#if VTRACE_FMB
    //cout << "Add non-ground clause " << c->toString() << endl;
#endif
    _clauses = _clauses->cons(c);

    // Only try and do this if the clause could decrease the maxModelSize
    if(c->length() < _maxModelSize){
      // This code attempts to detect a maximum model size from c either as e.g.
      // i) X=Y | X=Z | Y=Z  here we overestimate the model size
      // ii) X=a | X=b | X=f(a) again we might have a=b so we overestimate
      // do i) first
      unsigned posEqs = 0;
      for(unsigned i=0;i<c->length();i++){
        Literal* l = (*c)[i];
        if(l->isTwoVarEquality() && l->isPositive() && 
           (*l->nthArgument(0))!=(*l->nthArgument(1))
          ){ posEqs++; }
        else break;
      }
      // check if all literals are pos equalities
      if(posEqs == c->length() && c->varCnt() < _maxModelSize){
        _maxModelSize = c->varCnt();
      }      
      // then do ii) only if there are no posEqs (variable equalities)
      else if(posEqs==0){
        // okay is true if all literals are equalities of the form X=a or a=X for
        // the same X (svar)
        bool okay=true;
        int svar = -1;
        for(unsigned i=0;i<c->length();i++){
          Literal* l = (*c)[i];
          if(l->isEquality() && l->isPositive() && !l->isTwoVarEquality()){
            if(l->nthArgument(0)->isVar()){
              // arg 1 is term
              if(svar < 0){ svar = l->nthArgument(0)->var(); }
              else if(l->nthArgument(0)->var()!=(unsigned)svar){okay=false;break;}
            }
            else if(l->nthArgument(1)->isVar()){
              // arg 0 is term
              if(svar < 0){ svar = l->nthArgument(1)->var(); }
              else if(l->nthArgument(1)->var()!=(unsigned)svar){okay=false;break;}
            }   
            // both are terms, stop
            else{okay=false;break;}
          }
          // literal is not positive non-var equality, stop
          else{okay=false;break;}
        }
        if(okay && c->length() < _maxModelSize){
          _maxModelSize = _maxModelSize;
        }
      }
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

  // record the deleted functions and predicates
  // we do this here so that there are slots for symbols introduce in previous
  // preprocessing steps (definition introduction, splitting)
  del_f.ensure(env.signature->functions());
  del_p.ensure(env.signature->predicates());

  for(unsigned f=0;f<env.signature->functions();f++){
    del_f[f] = _deletedFunctions.find(f);
  }
  for(unsigned p=0;p<env.signature->predicates();p++){
    del_p[p] = _deletedPredicates.find(p);
  }

  // perform SortInference on ground and non-ground clauses
  // preprocessing should preserve sorts and doing this here means that introduced symbols get sorts
  {
    ASS(_clauses);
    TimeCounter tc(TC_FMB_SORT_INFERENCE);
    ClauseIterator cit = pvi(getConcatenatedIterator(ClauseList::Iterator(_clauses),ClauseList::Iterator(_groundClauses)));
    _sortedSignature = SortInference::apply(cit,del_f,del_p);
  }

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

  //TODO why is this here? Can intermediate steps introduce new functions?
  del_f.expand(env.signature->functions());

  // these offsets are for SAT variables and need to be set to the right size
  f_offsets.ensure(env.signature->functions());
  p_offsets.ensure(env.signature->predicates());

  // Set up fminbound, which records the minimum sort size for a function symbol
  // i.e. the smallest return or parameter sort
  // this loop also counts the number of constants in the problem
  _fminbound.ensure(env.signature->functions());
  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;

    if(env.signature->functionArity(f)==0) _constantCount++;

    // f might have been added to the signature since we created the sortedSignature
    // TODO how?
    if(f >= _sortedSignature->functionBounds.size()){
      _fminbound[f]=UINT_MAX;
      continue;
    }
    const DArray<unsigned>& b = _sortedSignature->functionBounds[f];
    unsigned min = b[0];
    for(unsigned i=1;i<b.size();i++){
      if(b[i]<min) min = b[i];
    }
    _fminbound[f]=min;
  }

  //Set up clause bounds
  {
    ClauseList::Iterator cit(_clauses);
    while(cit.hasNext()){
      Clause* c = cit.next();
      // will record the sort bounds of each variable used in the clause 
      // note that clauses have been normalized so variables go from 0 to varCnt
      DArray<unsigned>* bounds = new DArray<unsigned>(c->varCnt()); 
      for(unsigned i=0;i<bounds->size();i++){
        (*bounds)[i]=0; 
      }
      for(unsigned i=0;i<c->length();i++){
        Literal* lit = (*c)[i];
        if(lit->isEquality()){
          if(lit->isTwoVarEquality()) continue;
          ASS(lit->nthArgument(0)->isTerm());
          ASS(lit->nthArgument(1)->isVar());
          Term* t = lit->nthArgument(0)->term();
          const DArray<unsigned>& fbound = _sortedSignature->functionBounds[t->functor()];
          unsigned var = lit->nthArgument(1)->var();
          if((*bounds)[var]!=0){ ASS((*bounds)[var]==fbound[0]); }
          else{ 
            (*bounds)[var]=fbound[0]; 
          }
          for(unsigned j=0;j<t->arity();j++){
            ASS(t->nthArgument(j)->isVar());
            unsigned abound = fbound[j+1]; 
            unsigned avar = (t->nthArgument(j))->var();
            if((*bounds)[avar]!=0){ ASS((*bounds)[avar]==abound); }
            else{ 
              (*bounds)[avar]=abound;
            }
          }
        }
        else{
          for(unsigned j=0;j<lit->arity();j++){
            ASS(lit->nthArgument(j)->isVar());
            unsigned abound = _sortedSignature->predicateBounds[lit->functor()][j];
            unsigned avar = (lit->nthArgument(j))->var();
            if((*bounds)[avar]!=0){ ASS((*bounds)[avar]==abound); }
            else{ 
              (*bounds)[avar]=abound;
            }
          }
        }
      }
      // if anything doesn't have a bound then set it to max
      for(unsigned i=0;i<bounds->size();i++){
          if((*bounds)[i]==0){
            (*bounds)[i] = UINT_MAX;
          }
      }
      _clauseBounds.insert(c,bounds);
    } 
  }
} // init()

void FiniteModelBuilder::addGroundClauses(unsigned size)
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
        SATLiteral slit = getSATLiteral(f,emptyGrounding,(*c)[i]->polarity(),false,size);
        satClauseLits.push(slit);
      }
      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
  }
}

void FiniteModelBuilder::addNewInstances(unsigned size)
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
    const DArray<unsigned>& bounds = *_clauseBounds.get(c) ;
    static DArray<unsigned> mins;
    mins.ensure(fvars);

    //cout << "Mins: ";
    for(unsigned i=0;i<fvars;i++){
      mins[i] = min(bounds[i],size);
      //cout << mins[i] << " ";
    }
    //cout << endl;
    
    static DArray<unsigned> grounding;
    grounding.ensure(fvars);

    for(unsigned i=0;i<fvars;i++) grounding[i]=1;
    grounding[fvars-1]=0;

//TODO idea
// compute 'base' sat var by summing func/pred symbols then
// compute 'arity sum' per variable then
// can track the difference round the loop

instanceLabel:
    for(unsigned i=fvars-1;i+1!=0;i--){
     
      //Checking against mins skips instances where sort size restricts it
      if(grounding[i]==mins[i]){
        grounding[i]=1;
      } 
      else{
        grounding[i]++;
        // Grounding represents a new instance
        static SATLiteralStack satClauseLits;
        satClauseLits.reset();

        // Ground and translate each literal into a SATLiteral
        for(unsigned i=0;i<c->length();i++){
          Literal* lit = (*c)[i];

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
            satClauseLits.push(getSATLiteral(functor,use,lit->polarity(),true,size));
            
          }else{
            unsigned functor = lit->functor();
            unsigned arity = lit->arity();
            static DArray<unsigned> use;
            use.ensure(arity);

            for(unsigned j=0;j<arity;j++){
              ASS(lit->nthArgument(j)->isVar());
              use[j] = grounding[lit->nthArgument(j)->var()];
            }
            satClauseLits.push(getSATLiteral(functor,use,lit->polarity(),false,size));
          }
        }
     
        SATClause* satCl = SATClause::fromStack(satClauseLits);
        addSATClause(satCl);

        goto instanceLabel;
      }
    }
  }
}

void FiniteModelBuilder::addNewFunctionalDefs(unsigned size)
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

    const DArray<unsigned>& bounds = _sortedSignature->functionBounds[f];
    static DArray<unsigned> mins;
    mins.ensure(arity+2);

    //cout << "Mins: ";
    for(unsigned i=2;i<arity+2;i++){
      mins[i] = min(bounds[i-1],size);
      //cout << mins[i] << " ";
    }
    mins[0] = min(bounds[0],size);
    mins[1] = min(bounds[0],size);
    //cout << mins[arity] << " " << mins[arity+1] << endl;

      static DArray<unsigned> grounding;
      grounding.ensure(arity+2);
      for(unsigned i=0;i<arity+2;i++){ grounding[i]=1; }
      grounding[arity+1]=0;

newFuncLabel:
      for(unsigned i=arity+1;i+1!=0;i--){

        if(grounding[i]==mins[i]){
          grounding[i]=1;
        }
        else{
          grounding[i]++;
          //cout << "Grounding: ";
          //for(unsigned j=0;j<grounding.size();j++) cout << grounding[j] << " ";
          //cout << endl;
          if(grounding[0]>=grounding[1]){
            //cout << "Skipping" << endl;
            //Skip this instance
            goto newFuncLabel;
          }
          static SATLiteralStack satClauseLits;
          satClauseLits.reset();

          static DArray<unsigned> use;
          use.ensure(arity+1);
          for(unsigned k=0;k<arity;k++) use[k]=grounding[k+2];
          use[arity]=grounding[0];
          satClauseLits.push(getSATLiteral(f,use,false,true,size)); 
          use[arity]=grounding[1];
          satClauseLits.push(getSATLiteral(f,use,false,true,size)); 

          SATClause* satCl = SATClause::fromStack(satClauseLits);
          addSATClause(satCl);
          goto newFuncLabel;
        }
      }
  }
}

void FiniteModelBuilder::addNewSymmetryOrderingAxioms(unsigned size,
                       Stack<GroundedTerm>& groundedTerms, unsigned maxSize)
{
  CALL("FiniteModelBuilder::addNewSymmetryOrderingAxioms");


  // Add restricted totality 
  // i.e. for constant a1 add { a1=1 } and for a2 add { a2=1, a2=2 } and so on
  if(groundedTerms.length() < size) return;

  GroundedTerm gt = groundedTerms[size-1];

  unsigned arity = env.signature->functionArity(gt.f);
  static DArray<unsigned> grounding;
  grounding.ensure(arity+1);
  for(unsigned i=0;i<arity;i++) grounding[i] = gt.grounding;

  //cout << "Add symmetry ordering for " << gt.f << "," << gt.grounding << endl;

  static SATLiteralStack satClauseLits;
  satClauseLits.reset(); 
  for(unsigned i=1;i<=size;i++){
    grounding[arity]=i;
    SATLiteral sl = getSATLiteral(gt.f,grounding,true,true,maxSize);
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

      // do not add canonicity for functions
      if(arityi>0) return;

      static DArray<unsigned> grounding_i;
      grounding_i.ensure(arityi+1);
      for(unsigned a=0;a<arityi;a++){ grounding_i[a]=gti.grounding;}
      grounding_i[arityi]=size;
      satClauseLits.push(getSATLiteral(gti.f,grounding_i,false,true,maxSize));
 
      //cout << "Adding cannon for " << gti.f <<","<<gti.grounding<<endl;

      for(unsigned j=0;j<i;j++){
        GroundedTerm gtj = groundedTerms[j];
        unsigned arityj = env.signature->functionArity(gtj.f);
        static DArray<unsigned> grounding_j;
        grounding_j.ensure(arityj+1);
        for(unsigned a=0;a<arityj;a++){ grounding_j[a]=gtj.grounding;}
        grounding_j[arityj]=size-1;
        //cout << "with " <<gtj.f<<","<<gtj.grounding<<endl;

        satClauseLits.push(getSATLiteral(gtj.f,grounding_j,true,true,maxSize));
      }
      addSATClause(SATClause::fromStack(satClauseLits));
  }

}

void FiniteModelBuilder::addUseModelSize(unsigned size)
{
  CALL("FiniteModelBuilder::addUseModelSize");

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
          satClauseLits.push(getSATLiteral(gt.f,grounding,true,true,size)); 
        }
        else{
          for(unsigned m=1;m<=size;m++){
            //assume arity=1
            grounding[0]=m;
            satClauseLits.push(getSATLiteral(gt.f,grounding,true,true,size)); 
          }
        }
    }
  }

  addSATClause(SATClause::fromStack(satClauseLits));
}

void FiniteModelBuilder::addNewTotalityDefs(unsigned size)
{
  CALL("FiniteModelBuilder::addNewTotalityDefs");


  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;
    unsigned arity = env.signature->functionArity(f);

#if VTRACE_FMB
    cout << "Adding total defs for " << env.signature->functionName(f) << endl;
#endif

    const DArray<unsigned>& bounds = _sortedSignature->functionBounds[f];

    if(arity==0){
      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
      for(unsigned i=0;i<min(size,bounds[0]);i++){
        static DArray<unsigned> use(1);
        use[0]=i+1; 
        SATLiteral slit = getSATLiteral(f,use,true,true,size);
        satClauseLits.push(slit);
      }
      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl); 
      continue;
    }

    static DArray<unsigned> mins;
    mins.ensure(arity);
    for(unsigned i=0;i<arity;i++){
      mins[i] = min(bounds[i+1],size);
    }

      static DArray<unsigned> grounding;
      grounding.ensure(arity);
      for(unsigned i=0;i<arity;i++){ grounding[i]=1; }
      grounding[arity-1]=0;

newTotalLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(grounding[i]==mins[i]){
          grounding[i]=1;
        }
        else{
          grounding[i]++;
          //cout << "Grounding: ";
          //for(unsigned j=0;j<grounding.size();j++) cout << grounding[j] << " ";
          //cout << endl;

          static SATLiteralStack satClauseLits;
          satClauseLits.reset();

          for(unsigned j=0;j<min(size,bounds[0]);j++){
            static DArray<unsigned> use;
            use.ensure(arity+1);
            for(unsigned k=0;k<arity;k++) use[k]=grounding[k];
            use[arity]=j+1;
            satClauseLits.push(getSATLiteral(f,use,true,true,size));
          }
          SATClause* satCl = SATClause::fromStack(satClauseLits);
          addSATClause(satCl);
          goto newTotalLabel;
        }
      }
  }
}


SATLiteral FiniteModelBuilder::getSATLiteral(unsigned f, const DArray<unsigned>& grounding,
                                                           bool polarity,bool isFunction,unsigned size)
{
  CALL("FiniteModelBuilder::getSATLiteral");

  // cannot have predicate 0 here (it's equality)
  ASS(f>0 || isFunction);

  unsigned arity = isFunction ? env.signature->functionArity(f) : env.signature->predicateArity(f);
  ASS((isFunction && arity==grounding.size()-1) || (!isFunction && arity==grounding.size()));
  unsigned offset = isFunction ? f_offsets[f] : p_offsets[f];

/*
  vstring name = isFunction ? env.signature->functionName(f) : env.signature->predicateName(f);
  cout << "getSATLiteral [ " << name << "(";
  for(unsigned i=0;i<arity;i++) cout <<  grounding[i] << " "; 
  cout << ")";
  if(isFunction) cout << " = " << grounding[arity];
  cout << " ] = ";
*/

  unsigned var = offset;
  unsigned mult=1;
  for(unsigned i=0;i<grounding.size();i++){
    var += mult*(grounding[i]-1);
    mult *= size;
  }
//  cout << var << endl;

  return SATLiteral(var,polarity);
}

void FiniteModelBuilder::addSATClause(SATClause* cl)
{
  CALL("FiniteModelBuilder::addSATClause");
  cl = Preprocess::removeDuplicateLiterals(cl);
  if(!cl){ return; }
#if VTRACE_FMB
  cout << "ADDING " << cl->toString() << endl; // " of size " << cl->length() << endl;
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

  env.statistics->phase = Statistics::FMB_CONSTRAINT_GEN;

  if(env.property->category()==Property::EPR || _maxArity==0){
    ASS(_sortedSignature);
    unsigned max = 1;
    for(unsigned s=0;s<_sortedSignature->sorts;s++){
      unsigned c = (_sortedSignature->sortedConstants[s]).size();
      if(c>max){
        max = c; 
      }
    }
    if(max < _maxModelSize){
      _maxModelSize = max;
    }
  }
  if(_maxModelSize < UINT_MAX  && env.options->mode()!=Options::Mode::SPIDER){
      cout << "Detected maximum model size of " << _maxModelSize << endl;
  }

  unsigned modelSize = _useConstantsAsStart ? _constantCount : _startModelSize;

  if (reset(modelSize)) {
  while(true){
#if VTRACE_FMB
    cout << "TRYING " << modelSize << endl;
#endif
    if(env.options->mode()!=Options::Mode::SPIDER) { 
      cout << "TRYING " << modelSize << endl;
    }
    Timer::syncClock();
    if(env.timeLimitReached()){ return MainLoopResult(Statistics::TIME_LIMIT); }

    {
    TimeCounter tc(TC_FMB_CONSTRAINT_CREATION);

    // add the new clauses to _clausesToBeAdded
#if VTRACE_FMB
    cout << "GROUND" << endl;
#endif
    addGroundClauses(modelSize);
#if VTRACE_FMB
    cout << "INSTANCES" << endl;
#endif
    addNewInstances(modelSize);
#if VTRACE_FMB
    cout << "FUNC DEFS" << endl;
#endif
    addNewFunctionalDefs(modelSize);
#if VTRACE_FMB
    cout << "SYM DEFS" << endl;
#endif
    addNewSymmetryAxioms(modelSize);
    
#if VTRACE_FMB
    cout << "TOTAL DEFS" << endl;
#endif
    addNewTotalityDefs(modelSize);
#if VTRACE_FMB
    cout << "USE MODEL SIZE" << endl;
#endif
    //addUseModelSize(modelSize);

#if 0 
    // Say that first modelSize grounded terms are distinct experiment
    for(unsigned s=0;s<_sortedSignature->sorts;s++){
      Stack<GroundedTerm> gts = _sortedGroundedTerms[s];
      unsigned total = modelSize;
      if(total > gts.size()) total = gts.size(); 
      for(unsigned i=0;i<total;i++){
        GroundedTerm gt = gts[i];
        unsigned arity = env.signature->functionArity(gt.f);
        static DArray<unsigned> grounding;
        grounding.ensure(arity+1);
        for(unsigned a=0;a<arity;a++){ grounding[a]=gt.grounding;}
        if(arity==0){
          grounding[arity]=i+1;
          addSATClause(getSATLiteral(gt.f,grounding,true,true,modelSize));
        }
        else{
          static SATLiteralStack satClauseLits;
          satClauseLits.reset();
          for(unsigned j=1;j<=i;j++){
            grounding[arity]=j;
            satClauseLits.push(getSATLiteral(gt.f,grounding,true,true,modelSize));
          }
          addSATClause(SATClause::fromStack(satClauseLits));
        }
      }
    }
#endif
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
      satResult = _solver->solve();
      env.statistics->phase = Statistics::FMB_CONSTRAINT_GEN;
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
        if(env.property->category()==Property::EPR || _maxArity==0){
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

    // destroy the clauses
    SATClauseStack::Iterator it(_clausesToBeAdded);
    while (it.hasNext()) {
      it.next()->destroy();
    }
    // but the container needs to be empty for the next round in any case
    _clausesToBeAdded.reset();

    modelSize++;
    if(!reset(modelSize)) {
      break;
    }
  }
  }

  // reset returned false, we can't represent all the variables; giving up!

  if(env.options->mode()!=Options::Mode::SPIDER){
    cout << "Cannot represent all propositional literals internally" <<endl;
  }

  if(UIHelper::szsOutput) {
    env.beginOutput();
    env.out() << "% SZS status GaveUp for " << _opt.problemName() << endl;
    env.endOutput();
  }

  return MainLoopResult(Statistics::UNKNOWN);
}

void FiniteModelBuilder::onModelFound(unsigned modelSize)
{
 CALL("FiniteModelBuilder::onModelFound");
 // Don't do any output if proof is off
 if(_opt.proof()==Options::Proof::OFF){ 
   return; 
 }
 if(_opt.mode()==Options::Mode::SPIDER){
   reportSpiderStatus('-');
 }
 cout << "Found model of size " << modelSize << endl;

 //we need to print this early because model generating can take some time
 if(UIHelper::szsOutput) {
   env.beginOutput();
   env.out() << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
       << " for " << _opt.problemName() << endl << flush;
   env.endOutput();
   UIHelper::satisfiableStatusWasAlreadyOutput = true;
 }
  // Prevent timing out whilst the model is being printed
  Timer::setTimeLimitEnforcement(false);

  FiniteModel model(modelSize);

  //Record interpretation of constants
  for(unsigned f=0;f<env.signature->functions();f++){
    if(env.signature->functionArity(f)>0) continue;
    if(del_f[f]) continue;

    bool found=false;
    for(unsigned c=1;c<=modelSize;c++){
      static DArray<unsigned> grounding(1);
      grounding[0]=c;
      SATLiteral slit = getSATLiteral(f,grounding,true,true,modelSize);
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
    DArray<unsigned> args;
    grounding.ensure(arity+1);
    args.ensure(arity);
    for(unsigned i=0;i<arity;i++){
       grounding[i]=1;
       args[i]=1;
    }
    grounding[arity-1]=0;
    args[arity-1]=0;

    const DArray<unsigned>& bounds = _sortedSignature->functionBounds[f];
    static DArray<unsigned> mins;
    mins.ensure(arity+1);
    for(unsigned j=0;j<arity;j++){ mins[j]=bounds[j+1];}
    mins[arity]=bounds[0];

    //cout <<"mins   ";
    //for(unsigned j=0;j<arity;j++){ cout << mins[j] << ", ";};
    //cout << endl;

fModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(args[i]==modelSize){
          grounding[i]=1;
          args[i]=1;
        }
        else{
          if(args[i]<mins[i]){
            grounding[i]++;
          }
          args[i]++;

          //for(unsigned j=0;j<arity;j++){ cout << args[j] << ", ";}; 
          //cout << "          ";
          //for(unsigned j=0;j<arity;j++){ cout << grounding[j] << ", ";}; 
          //cout  << endl;

          bool found=false;
          for(unsigned c=1;c<=modelSize;c++){
            grounding[arity]=c;
            SATLiteral slit = getSATLiteral(f,grounding,true,true,modelSize);
            if(_solver->trueInAssignment(slit)){
              //if(found){ cout << "Error: multiple interpretations of " << name << endl; }
              ASS(!found);
              found=true;
              model.addFunctionDefinition(f,args,c);
            }
          }
          if(!found){
             // This means that there is no result for this input
             // This is a result of the finite sort bounding and the argument
             // says that we can equate this domain element to a smaller one below the bound
             //TODO fix this 
             //cout << "NOT FOUND" << endl; 
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
      SATLiteral slit = getSATLiteral(f,emptyG,true,false,modelSize);
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

    const DArray<unsigned>& bounds = _sortedSignature->predicateBounds[f];

pModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){
    
        if(args[i]==modelSize){
          grounding[i]=1;
          args[i]=1;
       }
        else{
          if(args[i]<bounds[i]){
            grounding[i]++;
          }
          args[i]++;
          bool res;
          if(!_trivialPredicates.find(f,res)){ 
            SATLiteral slit = getSATLiteral(f,grounding,true,false,modelSize);
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
    //del_f[f]=false;

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
      DArray<unsigned> grounding;
      grounding.ensure(arity);
      for(unsigned i=0;i<arity-1;i++) grounding[i]=1;
      grounding[arity-1]=0;
ffModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(grounding[i]==modelSize){
          grounding[i]=1;
        }
        else{
          grounding[i]++;

          Substitution subst;
          for(unsigned j=0;j<arity;j++){
            //cout << grounding[j] << " is " << model.getDomainConstant(grounding[j])->toString() << endl;
            subst.bind(vars[j],model.getDomainConstant(grounding[j]));
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
    unsigned arity = env.signature->predicateArity(f);
    if(!del_p[f] && !_partiallyDeletedPredicates.find(f)) continue;

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

    DArray<unsigned> grounding;
    grounding.ensure(arity);
    for(unsigned i=0;i<arity;i++) grounding[i]=1;
    grounding[arity-1]=0;
ppModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(grounding[i]==modelSize){
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
              subst.bind(vars[j],model.getDomainConstant(grounding[j]));
            }
            Formula* predDefGround = SubstHelper::apply(predDef,subst);
            //cout << predDefGround << endl;
            try{
              bool res = model.evaluate(
                new FormulaUnit(predDefGround,new Inference(Inference::INPUT),Unit::InputType::AXIOM));
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

}
