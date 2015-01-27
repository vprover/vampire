/**
 * @file Grounder.cpp
 * Implements class Grounder.
 */

#include <algorithm>

#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"

#include "Grounder.hpp"

using namespace Kernel;

/**
 * Return SATClauseIterator with SAT clauses that are results
 * of grounding of @c cl.
 * use_n indcates whether we record the source for use in niceness computation
 *
 * ignore_splits means that we will ground cl even if it has splits
 */
SATClauseIterator Grounder::ground(Clause* cl,bool use_n, bool ignore_splits)
{
  CALL("Grounder::ground(Clause*)");

  if(!ignore_splits && !cl->noSplits()) {
    NOT_IMPLEMENTED;
  }

  //cout << "grounding " << cl->toString() << endl;
  SATClause* gndNonProp = groundNonProp(cl,use_n);
  //cout<< "grounded is " << gndNonProp->toString()<<endl;

  SATInference* inf = new FOConversionInference(UnitSpec(cl));
  gndNonProp->setInference(inf);

  return pvi( getSingletonIterator(gndNonProp) );
}

/**
 * Return SATClause that is a result of grounding of the
 * non-propositional part of @c cl.
 *
 * The order of literals in @c cl is preserved.
 *
 * @param cl the clause
 * @param acc previously accumulated literals
 * @param use_n indcates whether we record the source for use in niceness computation
 * @param normLits if non-zero, array to receive normalized literals
 * (in the order of literals in the clause). Size of the array must be
 * at least equal to te size of the clause. There is one-to-one
 * correspondence between normalized literals and SAT literals.
 */
void Grounder::groundNonProp(Clause* cl, SATLiteralStack& acc, bool use_n, Literal** normLits)
{
  CALL("Grounder::groundNonProp/2");

  static DArray<Literal*> lits;

  unsigned clen = cl->length();

  if(normLits) {
    std::copy(cl->literals(), cl->literals()+clen, normLits);
  }
  else {
    lits.initFromArray(clen, *cl);
    normLits = lits.array();
  }

  normalize(clen, normLits);

  for(unsigned i=0; i<clen; i++) {
    SATLiteral lit = groundNormalized(normLits[i]);
    // this is recording the FO literal for niceness computation 
    if(use_n){
      //lit.recordSource((* cl)[i]); 
      ASS(_satSolver);
      _satSolver->recordSource(lit.var(),(*cl)[i]);
    }
    acc.push(lit);
  }
}

/**
 * Return SATClause that is a result of grounding of the
 * non-propositional part of @c cl.
 *
 * The order of literals in @c cl is preserved.
 *
 * @param cl the clause
 * @param use_n indcates whether we record the source for use in niceness computation
 * @param normLits if non-zero, array to receive normalized literals
 * (in the order of literals in the clause). Size of the array must be
 * at least equal to te size of the clause. There is one-to-one
 * correspondence between normalized literals and SAT literals.
 */
SATClause* Grounder::groundNonProp(Clause* cl, bool use_n, Literal** normLits)
{
  CALL("Grounder::groundNonProp(Clause*,Literal**)");

  static SATLiteralStack gndLits;
  gndLits.reset();

  groundNonProp(cl, gndLits, use_n, normLits);

  SATClause* res = SATClause::fromStack(gndLits);
  return res;
}

/**
 * Return SATLiteral corresponding to @c lit.
 * use_n indcates whether we record the source for use in niceness computation
 */
SATLiteral Grounder::ground(Literal* lit,bool use_n)
{
  CALL("Grounder::ground(Literal*)");

  Literal* norm = lit;
  normalize(1, &norm);
  SATLiteral slit = groundNormalized(norm);
  // this is recording the FO literal for niceness computation later
  if(use_n){
     ASS(_satSolver);
     _satSolver->recordSource(slit.var(),lit);
  }
  return slit;
}

/**
 * Return SATLiteral corresponding to @c lit.
 */
SATLiteral Grounder::groundNormalized(Literal* lit)
{
  CALL("Grounder::groundNormalized");

  if(_sat2fo){
    SATLiteral l =  _sat2fo->toSAT(lit);
    //cout << "groundNormalized " << lit->toString() << " is " << l.toString();
    return l; 
  }
  else{
    //cout << "no sat2fo" << endl;
  }

  bool isPos = lit->isPositive();
  Literal* posLit = Literal::positiveLiteral(lit);

  unsigned* pvar;
  if(_asgn.getValuePtr(posLit, pvar)) {
    *pvar = _nextSatVar++; 
  }
  return SATLiteral(*pvar, isPos);
}


LiteralIterator Grounder::groundedLits()
{
  CALL("Grounder::groundedLits");

  return _asgn.domain();
}

void Grounder::recordInference(Clause* origClause, SATClause* refutation, Clause* resultClause)
{
  CALL("Grounder::recordInference");
  ASS(refutation);

  static Stack<UnitSpec> prems;
  prems.reset();

  if(origClause) {
    prems.push(UnitSpec(origClause));
  }
  SATInference::collectFOPremises(refutation, prems);

  unsigned premCnt = prems.size();

  InferenceStore::FullInference* inf = new(premCnt) InferenceStore::FullInference(premCnt);
  inf->rule = Inference::GLOBAL_SUBSUMPTION;

  for(unsigned i=0; i<premCnt; i++) {
    inf->premises[i] = prems[i];
  }

  InferenceStore::instance()->recordInference(UnitSpec(resultClause), inf);
}

////////////////////////////////
// GlobalSubsumptionGrounder
//

struct GlobalSubsumptionGrounder::OrderNormalizingComparator
{
  Literal** _lits;
  OrderNormalizingComparator(Literal** lits) : _lits(lits) {}

  bool operator()(unsigned a, unsigned b) {
    Literal* la = _lits[a];
    Literal* lb = _lits[b];
    if(la==lb) { return false; }
    if(la->vars()!=lb->vars()) {
      //first, we want literals with less variables to appear in the
      //beginning as there is better chance to get some sharing across clauses
      return la->vars()<lb->vars();
    }
    if(la->weight()!=lb->weight()) {
      return la->weight()<lb->weight();
    }
    if(la->header()!=lb->header()) {
      return la->header()<lb->header();
    }
    //now get just some total deterministic order
    static DisagreementSetIterator dsit;
    dsit.reset(la, lb, false);
    ALWAYS(dsit.hasNext());
    pair<TermList,TermList> da = dsit.next();
    if(da.first.isVar()!=da.second.isVar()) {
      return da.first.isVar();
    }
    if(da.first.isVar()) {
      ASS_NEQ(da.first.var(),da.second.var());
      return da.first.var()<da.second.var();
    }
    else {
      ASS_NEQ(da.first.term()->functor(),da.second.term()->functor());
      return da.first.term()->functor()<da.second.term()->functor();
    }
    return a<b; //if nothing else applies, we keep the original order
  }
};

void GlobalSubsumptionGrounder::normalize(unsigned cnt, Literal** lits)
{
  CALL("GlobalSubsumptionGrounder::normalize");

  if(!_doNormalization) { return; }

  if(cnt==0) { return; }
  if(cnt==1) {
    lits[0] = Renaming::normalize(lits[0]);
  }

  static Stack<unsigned> litOrder;
  litOrder.reset();
  litOrder.loadFromIterator(getRangeIterator(0u,cnt));

  std::sort(litOrder.begin(), litOrder.end(), OrderNormalizingComparator(lits));

  static Renaming normalizer;
  normalizer.reset();

  for(unsigned i=0; i<cnt; i++) {
    unsigned li = litOrder[i];
    normalizer.normalizeVariables(lits[li]);
    lits[li] = normalizer.apply(lits[li]);
  }
}


/////////////////
// IGGrounder
//

IGGrounder::IGGrounder(SATSolver* satSolver) : Grounder(satSolver) 
{
  // For each sort select the most prolific constant

  DHMap<unsigned,unsigned> map; 
  // Search the constant function symbols
  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
     if(env.signature->functionArity(i)==0) {
       Signature::Symbol* sym = env.signature->getFunction(i);
       unsigned usage = sym->usageCnt();
       unsigned sort = sym->fnType()->result(); 
       if(!map.find(sort) || map.get(sort) < usage){
         cout << "selecting new constant for sort " << sort << " with usage " << usage << endl;
#if VDEBUG
         if(!map.find(sort)) cout << "new sort " << sort << endl;
         else cout << "old usage " << map.get(sort) << endl;
#endif
         _tgtTerms.set(sort,TermList(Term::createConstant(i)));
         map.set(sort,usage);
       }
     }
  }
 
  // Some sorts may not have constants in the problem so we should create some
  // For this we should check the sorts of variables but I don't have this
  // So instead we will create constants for all builtin sorts and user-defined sorts
  //   that do not already exist in map
  
  // First we consider builtin sorts
  if(!map.find(Sorts::SRT_INTEGER)){
    unsigned constant = env.signature->addIntegerConstant("0",false);
    _tgtTerms.set(Sorts::SRT_INTEGER,TermList(Term::createConstant(constant)));
  }
  if(!map.find(Sorts::SRT_REAL)){
    unsigned constant = env.signature->addRealConstant("0",false);
    _tgtTerms.set(Sorts::SRT_REAL,TermList(Term::createConstant(constant)));
  }
  if(!map.find(Sorts::SRT_RATIONAL)){
    unsigned constant = env.signature->addRationalConstant("1","1",false);
    _tgtTerms.set(Sorts::SRT_RATIONAL,TermList(Term::createConstant(constant)));
  } 

  // Next user-defined sorts
  for(unsigned sort = Sorts::FIRST_USER_SORT;sort<env.sorts->sorts();sort++){ 
    if(!map.find(sort)){
      bool added;
      unsigned constant = env.signature->addFunction("$default_"+env.sorts->sortName(sort),0,added);
      ASS(added);
      Signature::Symbol* symbol = env.signature->getFunction(constant);
      symbol->setType(BaseType::makeType(0,0,sort));
      _tgtTerms.set(sort,TermList(Term::createConstant(constant)));
    }
  }
}

class IGGrounder::CollapsingApplicator
{
  Literal* _lit;
  IGGrounder* _parent;
public:
  CollapsingApplicator(Literal* lit,IGGrounder* parent) : _lit(lit), _parent(parent) {}
  TermList apply(unsigned var)
  {
    unsigned sort = SortHelper::getVariableSort(var,_lit);
    return _parent->getConstant(sort);
  }
};

/**
 * Return literal that has all variables replaced by variable
 * number zero.
 */
Literal* IGGrounder::collapseVars(Literal* lit)
{
  CALL("IGGrounder::collapseVars");
  ASS(lit);

  CollapsingApplicator apl(lit,this);
  return SubstHelper::apply(lit, apl);
}

void IGGrounder::normalize(unsigned cnt, Literal** lits)
{
  CALL("IGGrounder::normalize");

  for(unsigned i=0; i<cnt; i++) {
    lits[i] = collapseVars(lits[i]);
  }
}

