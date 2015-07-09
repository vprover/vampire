/**
 * @file FiniteModelBuilderNonIncremental.cpp
 * Implements class FiniteModelBuilderNonIncremental.
 */

#include <math.h>

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
#include "Shell/TPTPPrinter.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/GeneralSplitting.hpp"

#include "ClauseFlattening.hpp"
#include "SortInference.hpp"
#include "DefinitionIntroduction.hpp"
#include "FiniteModelBuilderNonIncremental.hpp"

#define VTRACE_FMB 0

namespace FMB 
{

FiniteModelBuilderNonIncremental::FiniteModelBuilderNonIncremental(Problem& prb, const Options& opt)
: MainLoop(prb, opt), _groundClauses(0), _clauses(0), _sortedSignature(0), 
                      _isComplete(true), _maxModelSize(UINT_MAX), _constantCount(0)
{
  CALL("FiniteModelBuilderNonIncremental::FiniteModelBuilderNonIncremental");

  if(!opt.complete(prb)){
    _isComplete = false;
    return;
  }
  _startModelSize = opt.fmbStartSize();
  _useConstantsAsStart = opt.fmbStartWithConstants();
  _symmetryRatio = opt.fmbSymmetryRatio();

  _deletedFunctions.loadFromMap(prb.getEliminatedFunctions());
  _deletedPredicates.loadFromMap(prb.getEliminatedPredicates());

  _maxArity = 0;
  for(unsigned f=0;f<env.signature->functions();f++){
    unsigned arity = env.signature->functionArity(f);
    if(arity>_maxArity) _maxArity = arity;
  }

}

bool FiniteModelBuilderNonIncremental::reset(unsigned size){
  CALL("FiniteModelBuilderNonIncremental::reset");

  unsigned offsets=1;
  for(unsigned f=0; f<env.signature->functions();f++){
    if(del_f[f]) continue; 
    unsigned arity=env.signature->functionArity(f);
    //cout << f << "("<<arity<<") has " << offsets << endl;
    f_offsets[f]=offsets;
    unsigned add = pow(size,arity+2);
    if(UINT_MAX - add < offsets){
      return false;
    }
    offsets += add;
  }
  for(unsigned p=1; p<env.signature->predicates();p++){
    if(del_p[p]) continue;
    unsigned arity=env.signature->predicateArity(p);
    //cout << p << "("<<arity<<") has " << offsets << endl;
    p_offsets[p]=offsets;
    unsigned add = pow(size,arity+1);
    if(UINT_MAX - add < offsets){
      return false;
    }
    offsets += add; 
  }
  //cout << "Maximum offset is " << offsets << endl;

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

  _solver->ensureVarCount(offsets+1);

  _sortedGroundedTerms.ensure(_sortedSignature->sorts);
  for(unsigned s=0;s<_sortedSignature->sorts;s++){
    _sortedGroundedTerms[s].reset();
    for(unsigned c=0;c<_sortedSignature->sortedConstants[s].length();c++){
      GroundedTerm g;
      g.f = _sortedSignature->sortedConstants[s][c];
      g.grounding = 0;
      _sortedGroundedTerms[s].push(g);
      //cout << "Adding " << g.f << "," << g.grounding << " to " << s << endl;
    }
    for(unsigned m=1;m<size;m++){
      for(unsigned f=0;f<_sortedSignature->sortedFunctions[s].length();f++){
        GroundedTerm g;
        g.f =_sortedSignature->sortedFunctions[s][f];
        g.grounding = 1+((m+f)%(size-1));
        _sortedGroundedTerms[s].push(g);
        //cout << "Adding " << g.f << "," << g.grounding << " to " << s << endl;
      }
    }

  }

  return true;
}

void FiniteModelBuilderNonIncremental::init()
{
  CALL("FiniteModelBuilderNonIncremental::init");

  if(!_isComplete) return;


  env.statistics->phase = Statistics::FMB_PREPROCESSING;

  // Perform DefinitionIntroduction as we iterate
  // over the clauses of the problem
  DefinitionIntroduction cit = DefinitionIntroduction(_prb.clauseIterator());
  //ClauseIterator cit = _prb.clauseIterator();
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

  del_f.ensure(env.signature->functions());
  del_p.ensure(env.signature->predicates());

  for(unsigned f=0;f<env.signature->functions();f++){
    del_f[f] = _deletedFunctions.find(f);
  }
  for(unsigned p=0;p<env.signature->predicates();p++){
    del_p[p] = _deletedPredicates.find(p);
  }

  {
    TimeCounter tc(TC_FMB_SORT_INFERENCE);
    ClauseIterator cit= pvi(getConcatenatedIterator(
                        ClauseList::Iterator(_clauses),
                        ClauseList::Iterator(_groundClauses)));    
    _sortedSignature = SortInference::apply(cit,del_f,del_p);
  }

  del_f.expand(env.signature->functions());

  f_offsets.ensure(env.signature->functions());
  p_offsets.ensure(env.signature->predicates());

  //Set up fminbound
  _fminbound.ensure(env.signature->functions());
  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;

    if(env.signature->functionArity(f)==0) _constantCount++;

    if(f >= _sortedSignature->functionBounds.size()){
      _fminbound[f]=UINT_MAX;
      continue;
    }
    DArray<unsigned> b = _sortedSignature->functionBounds[f];
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
      DArray<unsigned>* bounds = new DArray<unsigned>(c->varCnt()); 
      for(unsigned i=0;i<bounds->size();i++){
        (*bounds)[i]=0; 
      }
      bool allTwoVar = true;
      for(unsigned i=0;i<c->length();i++){
        Literal* lit = (*c)[i];
        if(lit->isEquality()){
          if(lit->isTwoVarEquality()) continue;
          allTwoVar=false;
          ASS(lit->nthArgument(0)->isTerm());
          ASS(lit->nthArgument(1)->isVar());
          Term* t = lit->nthArgument(0)->term();
          DArray<unsigned> fbound = _sortedSignature->functionBounds[t->functor()];
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
          allTwoVar=false;
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
#if VDEBUG
      if(!allTwoVar){
        for(unsigned i=0;i<bounds->size();i++){
          ASS((*bounds)[i]>0);
        }
      }
#endif
      _clauseBounds.insert(c,bounds);
    } 
  }
}

void FiniteModelBuilderNonIncremental::addGroundClauses()
{
  CALL("FiniteModelBuilderNonIncremental::addGroundClauses");

  // If we don't have any ground clauses don't do anything
  if(!_groundClauses) return;

  ClauseList::Iterator cit(_groundClauses);

  // Note ground clauses will consist of predicates only
  DArray<unsigned> emptyGrounding(0);
  while(cit.hasNext()){

      Clause* c = cit.next();
      ASS(c);

      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
      for(unsigned i=0;i<c->length();i++){
        unsigned f = (*c)[i]->functor();
        SATLiteral slit = getSATLiteral(f,emptyGrounding,(*c)[i]->polarity(),false,0);
        satClauseLits.push(slit);
      }
      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl);
  }
}

void FiniteModelBuilderNonIncremental::addNewInstances(unsigned size)
{
  CALL("FiniteModelBuilderNonIncremental::addNewInstances");

  ClauseList::Iterator cit(_clauses); 

  while(cit.hasNext()){
    Clause* c = cit.next();
    ASS(c);
#if VTRACE_FMB
    cout << "Instances of " << c->toString() << endl;
#endif

    unsigned fvars = c->varCnt();
    DArray<unsigned> bounds = *_clauseBounds.get(c) ;
    DArray<unsigned> mins(fvars);
    //cout << "Mins: ";
    for(unsigned i=0;i<fvars;i++){
      mins[i] = min(bounds[i],size);
      //cout << mins[i] << " ";
    }
    //cout << endl;
    
    DArray<unsigned> grounding(fvars);
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
#if VTRACE_FMB
        //cout << "Grounding: ";
        //for(unsigned j=0;j<grounding.size();j++) cout << grounding[j] << " ";
        //cout << endl;
#endif

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
            DArray<unsigned> use(arity+1);
            for(unsigned j=0;j<arity;j++){
              ASS(t->nthArgument(j)->isVar());
              use[j] = grounding[t->nthArgument(j)->var()];
            }
            use[arity]=grounding[lit->nthArgument(1)->var()];
            satClauseLits.push(getSATLiteral(functor,use,lit->polarity(),true,size));
            
          }else{
            unsigned functor = lit->functor();
            unsigned arity = lit->arity();
            DArray<unsigned> use(arity);
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

void FiniteModelBuilderNonIncremental::addNewFunctionalDefs(unsigned size)
{
  CALL("FiniteModelBuilderNonIncremental::addNewFunctionalDefs");

  // For each function f of arity n we add the constraint 
  // f(x1,...,xn) != y | f(x1,...,xn) != z 
  // they should be instantiated with groundings where y!=z

  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;
    unsigned arity = env.signature->functionArity(f);

#if VTRACE_FMB
    cout << "Adding func defs for " << env.signature->functionName(f) << endl;
#endif

    DArray<unsigned> bounds = _sortedSignature->functionBounds[f];
    DArray<unsigned> mins(arity+2);
    //cout << "Mins: ";
    for(unsigned i=0;i<arity;i++){
      mins[i] = min(bounds[i+1],size);
      //cout << mins[i] << " ";
    }
    mins[arity] = min(bounds[0],size);
    mins[arity+1] = min(bounds[0],size);
    //cout << mins[arity] << " " << mins[arity+1] << endl;

      DArray<unsigned> grounding(arity+2);
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

          DArray<unsigned> use(arity+1);
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

void FiniteModelBuilderNonIncremental::addNewSymmetryOrderingAxioms(unsigned size,
                       Stack<GroundedTerm>& groundedTerms)
{
  CALL("FiniteModelBuilderNonIncremental::addNewSymmetryOrderingAxioms");


  // Add restricted totality 
  // i.e. for constant a1 add { a1=1 } and for a2 add { a2=1, a2=2 } and so on
  if(groundedTerms.length() < size) return;

  GroundedTerm gt = groundedTerms[size-1];
  unsigned arity = env.signature->functionArity(gt.f);
  DArray<unsigned> grounding(arity+1);
  for(unsigned i=0;i<arity;i++) grounding[i] = gt.grounding;

  //cout << "Add symmetry ordering for " << gt.f << "," << gt.grounding << endl;

  static SATLiteralStack satClauseLits;
  satClauseLits.reset(); 
  for(unsigned i=1;i<=size;i++){
    grounding[arity]=i;
    SATLiteral sl = getSATLiteral(gt.f,grounding,true,true,size);
    satClauseLits.push(sl);
  }
  SATClause* satCl = SATClause::fromStack(satClauseLits);
  addSATClause(satCl);

}

void FiniteModelBuilderNonIncremental::addNewSymmetryCanonicityAxioms(unsigned size,
                       Stack<GroundedTerm>& groundedTerms,
                       unsigned maxSize)
{
  CALL("FiniteModelBuilderNonIncremental::addNewSymmetryCanonicityAxioms");

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
      DArray<unsigned> grounding_i(arityi+1);
      for(unsigned a=0;a<arityi;a++){ grounding_i[a]=gti.grounding;}
      grounding_i[arityi]=size;
      satClauseLits.push(getSATLiteral(gti.f,grounding_i,false,true,size));
 
      //cout << "Adding cannon for " << gti.f <<","<<gti.grounding<<endl;

      for(unsigned j=0;j<i;j++){
        GroundedTerm gtj = groundedTerms[j];
        unsigned arityj = env.signature->functionArity(gtj.f);
        DArray<unsigned> grounding_j(arityj+1);
        for(unsigned a=0;a<arityj;a++){ grounding_j[a]=gtj.grounding;}
        grounding_j[arityj]=size-1;
        //cout << "with " <<gtj.f<<","<<gtj.grounding<<endl;

        satClauseLits.push(getSATLiteral(gtj.f,grounding_j,true,true,size));
      }
      addSATClause(SATClause::fromStack(satClauseLits));
  }

}

void FiniteModelBuilderNonIncremental::addUseModelSize(unsigned size)
{
  CALL("FiniteModelBuilderNonIncremental::addUseModelSize");

  // Only do thise if we have unary functions at most
  if(_maxArity>1) return;

  static SATLiteralStack satClauseLits;
  satClauseLits.reset();

  for(unsigned s=0;s<_sortedSignature->sorts;s++){ 
    DArray<unsigned> cgrounding(1);
    cgrounding[0]=size;
    for(unsigned c=0;c<_sortedSignature->sortedConstants[s].size();c++){
      satClauseLits.push(
        getSATLiteral(_sortedSignature->sortedConstants[s][c],cgrounding,true,true,size)); 
    }
    DArray<unsigned> fgrounding(2);
    fgrounding[1]=size;
    for(unsigned i=1;i<=size;i++){
      fgrounding[0]=i;
      for(unsigned f=0;f<_sortedSignature->sortedFunctions[f].size();f++){
        satClauseLits.push(
          getSATLiteral(_sortedSignature->sortedFunctions[s][f],fgrounding,true,true,size)); 
      } 
    }
  }

  addSATClause(SATClause::fromStack(satClauseLits));
}

void FiniteModelBuilderNonIncremental::addNewTotalityDefs(unsigned size)
{
  CALL("FiniteModelBuilderNonIncremental::addNewTotalityDefs");


  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;
    unsigned arity = env.signature->functionArity(f);

#if VTRACE_FMB
    cout << "Adding total defs for " << env.signature->functionName(f) << endl;
#endif

    DArray<unsigned> bounds = _sortedSignature->functionBounds[f];

    if(arity==0){
      static SATLiteralStack satClauseLits;
      satClauseLits.reset();
      for(unsigned i=0;i<min(size,bounds[0]);i++){
        DArray<unsigned> use(1);
        use[0]=i+1; 
        SATLiteral slit = getSATLiteral(f,use,true,true,size);
        satClauseLits.push(slit);
      }
      SATClause* satCl = SATClause::fromStack(satClauseLits);
      addSATClause(satCl); 
      continue;
    }

    DArray<unsigned> mins(arity);
    for(unsigned i=0;i<arity;i++){
      mins[i] = min(bounds[i+1],size);
    }

      DArray<unsigned> grounding(arity);
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
            DArray<unsigned> use(arity+1);
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


SATLiteral FiniteModelBuilderNonIncremental::getSATLiteral(unsigned f, DArray<unsigned> grounding, 
                                                           bool polarity,bool isFunction,unsigned size)
{
  CALL("FiniteModelBuilderNonIncremental::getSATLiteral");

  // cannot have predicate 0 here
  ASS(f>0 || isFunction);

  unsigned arity = isFunction ? env.signature->functionArity(f) : env.signature->predicateArity(f);
  //cout << "getSATLiteral " << f<< "," << grounding.size() << "," << isFunction << "," << size << "," << arity << endl; 
  ASS((isFunction && arity==grounding.size()-1) || (!isFunction && arity==grounding.size()));
  unsigned offset = isFunction ? f_offsets[f] : p_offsets[f];

  //cout << "getSATLiteral " << f<< ","  << size << "," << offset << ", grounding = ";
  //for(unsigned i=0;i<grounding.size();i++) cout <<  grounding[i] << " "; 
  //cout << endl;

  unsigned var = offset;
  unsigned mult=1;
  for(unsigned i=0;i<grounding.size();i++){
    var += mult*(grounding[i]-1);
    mult *= size;
  }
  //cout << "return " << var << endl;

  return SATLiteral(var,polarity);
}

void FiniteModelBuilderNonIncremental::addSATClause(SATClause* cl)
{
  CALL("FiniteModelBuilderNonIncremental::addSATClause");
  cl = Preprocess::removeDuplicateLiterals(cl);
  if(!cl){ return; }
#if VTRACE_FMB
  cout << "ADDING " << cl->toString() << endl;
#endif

  _clausesToBeAdded.push(cl);

}

MainLoopResult FiniteModelBuilderNonIncremental::runImpl()
{
  CALL("FiniteModelBuilderNonIncremental::runImpl");

  if(!_isComplete){
    // give up!
    return MainLoopResult(Statistics::UNKNOWN);
  }

  env.statistics->phase = Statistics::FMB_CONSTRAINT_GEN;

  if(env.property->category()==Property::EPR){// || _useConstantsAsStart){
    ASS(_sortedSignature);
    unsigned max = 1;
    for(unsigned s=0;s<_sortedSignature->sorts;s++){
      unsigned c = (_sortedSignature->sortedConstants[s]).size();
      if(c>max){
        max = c; 
      }
    }
    //if(env.property->category()==Property::EPR){
      _maxModelSize = max;
    //}
    //if(_useConstantsAsStart){
    //  _startModelSize = max;
    //}
  }
  if(_maxModelSize < UINT_MAX  && env.options->mode()!=Options::Mode::SPIDER){
      cout << "Detected maximum model size of " << _maxModelSize << endl;
  }

  unsigned modelSize = _useConstantsAsStart ? _constantCount : _startModelSize;
  ALWAYS(reset(modelSize));
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
    addGroundClauses();
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

    // destroy the clauses
    SATClauseStack::Iterator it(_clausesToBeAdded);
    while (it.hasNext()) {
      it.next()->destroy();
    }
    // but the container needs to be empty for the next round in any case
    _clausesToBeAdded.reset();

    modelSize++;
    if(!reset(modelSize)){
      if(env.options->mode()!=Options::Mode::SPIDER){
        cout << "Cannot represent all propositional literals internally" <<endl;
      }
      return MainLoopResult(Statistics::UNKNOWN);
    }
  }


  return MainLoopResult(Statistics::UNKNOWN);
}

void FiniteModelBuilderNonIncremental::onModelFound(unsigned modelSize)
{
 // Don't do any output if proof is off
 if(_opt.proof()==Options::Proof::OFF){ 
   return; 
 }
 if(_opt.mode()==Options::Mode::SPIDER){
   reportSpiderStatus('-');
 }
 cout << "Found model of size " << modelSize << endl;

 //we need to print this early because model generating can take some time
 if(UIHelper::cascMode) {
   env.beginOutput();
   env.out() << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
       << " for " << _opt.problemName() << endl << flush;
   env.endOutput();
   UIHelper::satisfiableStatusWasAlreadyOutput = true;
 }
  // Prevent timing out whilst the model is being printed
  Timer::setTimeLimitEnforcement(false);

  vostringstream modelStm;
  bool printIntroduced = false; 

  //Output domain
  modelStm << "fof(domain,interpretation_domain," << endl;
  modelStm << "      ! [X] : (" << endl;
  modelStm << "         ";
  for(unsigned i=1;i<=modelSize;i++){
  modelStm << "X = fmb" << i;
  if(i<modelSize) modelStm << " | ";
  if(i==modelSize) modelStm << endl;
  else if(i%5==0) modelStm << endl << "         ";
  }
  modelStm << "      ) )." <<endl;
  //Distinctness of domain
  modelStm << endl;
  if(modelSize>1){
  modelStm << "fof(distinct_domain,interpreted_domain," << endl;
  modelStm << "         ";
  unsigned c=0;
  for(unsigned i=1;i<=modelSize;i++){
    for(unsigned j=i+1;j<=modelSize;j++){
      c++;
      modelStm << "fmb"<<i<<" != fmb"<<j;
      if(!(i==modelSize-1 && j==modelSize)){
         modelStm << " & ";
         if(c%5==0){ modelStm << endl << "         "; }
      }
      else{ modelStm << endl; }
    }
  }
  modelStm << ")." << endl << endl;
  }

  //Output interpretation of constants
  for(unsigned f=0;f<env.signature->functions();f++){
    if(env.signature->functionArity(f)>0) continue;
    if(!printIntroduced && env.signature->getFunction(f)->introduced()) continue;
    if(del_f[f]){
      Literal* def = _deletedFunctions.get(f);
      Clause* defc = new(1) Clause(1,Unit::AXIOM,new Inference(Inference::DEFINITION_UNFOLDING));
      (*defc)[0]=def;
      modelStm << TPTPPrinter::toString(defc) << endl;
      continue;
    }
    vstring name = env.signature->functionName(f);
    modelStm << "fof(constant_"<<name<<",functors,"<<name<< " = ";
    bool found=false;
    for(unsigned c=1;c<=modelSize;c++){
      DArray<unsigned> grounding(1);
      grounding[0]=c;
      SATLiteral slit = getSATLiteral(f,grounding,true,true,modelSize);
      if(_solver->trueInAssignment(slit)){
        //if(found){ cout << "Error: multiple interpretations of " << name << endl;}
        ASS(!found);
        modelStm << "fmb" << c;
        found=true;
      }
    }
    ASS(found);
    modelStm << ")."<<endl;
  }
  modelStm << endl;

  //Output interpretation of functions 
  for(unsigned f=0;f<env.signature->functions();f++){
    unsigned arity = env.signature->functionArity(f);
    if(arity==0) continue;
    if(!printIntroduced && env.signature->getFunction(f)->introduced()) continue;
    if(del_f[f]){
      Literal* def = _deletedFunctions.get(f);
      Clause* defc = new(1) Clause(1,Unit::AXIOM,new Inference(Inference::DEFINITION_UNFOLDING));
      (*defc)[0]=def;
      modelStm << TPTPPrinter::toString(defc) << endl;
      continue;
    }
    vstring name = env.signature->functionName(f);
    modelStm << "fof(function_"<<name<<",functors,"<<endl;

    DArray<unsigned> grounding(arity+1);
    for(unsigned i=0;i<arity;i++) grounding[i]=1;
    grounding[arity-1]=0;
    bool first=true;
    //cout << "Searching... " << name << " of " << arity << endl;
fModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){

        if(grounding[i]==modelSize){
          grounding[i]=1;
        }
        else{
          grounding[i]++;
          //cout << "Grounding: ";
          //for(unsigned j=0;j<grounding.size();j++) cout << grounding[j] << " ";
          //cout << endl;

          unsigned foundc;
          bool found=false;
          for(unsigned c=1;c<=modelSize;c++){
            grounding[arity]=c;
            SATLiteral slit = getSATLiteral(f,grounding,true,true,modelSize);
            if(_solver->trueInAssignment(slit)){
              //cout << "found " << c << endl;
              //if(found){ cout << "Error: multiple interpretations of " << name << endl; }
              ASS(!found);
              foundc=c;
              found=true;
            }
          }
          if(!found) goto fModelLabel; 

          if(!first){
            modelStm << " & " << endl;
          }
          first=false;
          modelStm << "         " << name << "(";
          for(unsigned j=0;j<arity;j++){
            if(j!=0) modelStm << ",";
            modelStm << "fmb" << grounding[j];
          }
          modelStm << ") = fmb" <<foundc;

          goto fModelLabel;
        }
      }
    modelStm << endl << ")." << endl << endl;
  }

  //Output interpretation of prop symbols 
  DArray<unsigned> emptyG(0);
  for(unsigned f=1;f<env.signature->predicates();f++){
    if(env.signature->predicateArity(f)>0) continue;
    if(!printIntroduced && env.signature->getPredicate(f)->introduced()) continue;
    if(del_p[f]){
      Unit* def = _deletedPredicates.get(f);
      modelStm << TPTPPrinter::toString(def) << endl; 
      continue;
    }
    vstring name = env.signature->predicateName(f);
    modelStm << "fof(predicate_"<<name<<",predicates,";
    SATLiteral slit = getSATLiteral(f,emptyG,true,false,modelSize);
    if(!_solver->trueInAssignment(slit)){ modelStm << "~"; }
    modelStm << name << ")."<<endl;
  }
  modelStm << endl;

//Output interpretation of predicates 
  for(unsigned f=1;f<env.signature->predicates();f++){
    unsigned arity = env.signature->predicateArity(f);
    if(arity==0) continue;
    if(!printIntroduced && env.signature->getPredicate(f)->introduced()) continue;
    if(del_p[f]){
      Unit* def = _deletedPredicates.get(f);
      modelStm << TPTPPrinter::toString(def) << endl; 
      continue;
    }
    vstring name = env.signature->predicateName(f);
    modelStm << "fof(predicate_"<<name<<",predicates,"<<endl;

    DArray<unsigned> grounding(arity);
    for(unsigned i=0;i<arity-1;i++) grounding[i]=1;
    grounding[arity-1]=0;
    bool first=true;
pModelLabel:
      for(unsigned i=arity-1;i+1!=0;i--){
    
        if(grounding[i]==modelSize){
          grounding[i]=1;
        }
        else{
          grounding[i]++;
          if(!first){
            modelStm << " & " << endl;
          }
          first=false;
          modelStm << "         ";
          SATLiteral slit = getSATLiteral(f,grounding,true,false,modelSize);
          if(!_solver->trueInAssignment(slit)){
            modelStm << "~";
          }

          modelStm << name << "(";
          for(unsigned j=0;j<arity;j++){
            if(j!=0) modelStm << ",";
            modelStm << "fmb" << grounding[j];
          }
          modelStm << ") ";

          goto pModelLabel;
        }
      }
    modelStm << endl << ")." << endl << endl;
  }


  env.statistics->model = modelStm.str();
}

}
