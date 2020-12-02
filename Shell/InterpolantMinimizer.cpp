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
 * @file InterpolantMinimizer.cpp
 * Implements class InterpolantMinimizer.
 */

#include <fstream>
#include <sstream>

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/MainLoop.hpp"

#include "Indexing/ClauseVariantIndex.hpp"

#include "Interpolants.hpp"
#include "Options.hpp"

#include "Saturation/Splitter.hpp"

#include "InterpolantMinimizer.hpp"


using namespace Shell;
using namespace Indexing;

#define TRACE(x)

/**
 * Return minimized interpolant of @c refutation
 * it traverses the proof and collects grey formulas.
 * For each grey formula, it adds digest and fringe properties (with case distinction between leaves and non-leaves).
 * Using these properties, the interpolant is minimized wrt its cost
 */
Formula* InterpolantMinimizer::getInterpolant(Unit* refutation)
{
  CALL("InterpolantMinimizer::getInterpolant");
  
  traverse(refutation);
  addAllFormulas();

  SMTSolverResult res;
  YicesSolver solver;
  YicesSolver::MinimizationResult mres = solver.minimize(_resBenchmark, costFunction(), res);


  DHSet<Unit*> slicedOff;

  if(mres==SMTSolver::FAIL) {
    cerr << "Minimization timed failed to find a satisfiable assignment, generating basic interpolant" << endl;
    goto just_generate_interpolant;
  }
  if(mres==SMTSolver::APPROXIMATE) {
    cerr << "Minimization gave approximate result" << endl;
  }

  if(_showStats) {
    env.beginOutput();
    env.out() << _statsPrefix << " cost: " <<res.assignment.get(costFunction()) << endl;
    env.endOutput();
  }

  collectSlicedOffNodes(res, slicedOff);

just_generate_interpolant:
  Formula* interpolant = Interpolants(&slicedOff).getInterpolant(refutation);
    
  return interpolant;
}

/*print formulas in SMT*/
    
void InterpolantMinimizer::prettyPrint(Formula* formula, ostream& out)
{
  CALL("SMTLibPrinter::prettyPrint");
        
  Signature *sig = env.signature;
  unsigned symbNum;
  Symbol* symb;
  TermList* args;
  FormulaList* fs;
  switch (formula->connective()) {
    case LITERAL:
        symbNum = formula->literal()->functor();
        symb = sig->getPredicate(symbNum);
        
        if(formula->literal()->args()->isNonEmpty())
             out << "(";
                
        prettyPrint(symb, out);
                
        args = formula->literal()->args();
        while(args->isNonEmpty()) {
                out << " ";
                if(args->isVar())
                    out << "x" << args->var();
                else
                    prettyPrint(args->term(), out);
                args = args->next();
            }
                
        if(formula->literal()->args()->isNonEmpty())
                out << ")";
                
        return;
    case AND:
    case OR:
        if(formula->connective() == AND)
            out << "(and ";
        else
            out << "(or ";
                
        for(fs = formula->args(); FormulaList::isNonEmpty(fs); fs = fs->tail()) {
            prettyPrint(fs->head(), out);
            out << " ";
        }
                
        out << ")";
        return;
    case IMP:
    case IFF:
    case XOR:
        if(formula->connective() == IMP)
                out << "(implies ";
        else if(formula->connective() == IFF)
            out << "(= ";
        else
            ASS(false);
                
        prettyPrint(formula->left(), out);
        out << " ";
        prettyPrint(formula->right(), out);
        out << ")";
        return;
    case NOT:
        out << "(not ";
        prettyPrint(formula->uarg(), out);
        out << ")";
        return;
    case FORALL:
        return;
    case EXISTS:
        return;
    case BOOL_TERM:
        out << formula->getBooleanTerm().toString();
        return;
    case TRUE:
        out << "true";
        return;
    case FALSE:
        out << "false";
        return;
    default:
        out << "WARNING!!! This is not a literal\n";
        ASS(false);
        return;
    }
}
    

    
/*print terms in SMT*/    
void InterpolantMinimizer::prettyPrint(Term* term, ostream& out)
{
    Signature *sig = env.signature;
    unsigned int symbNum = term->functor();
    Symbol* symb = sig->getFunction(symbNum);
        
    if(term->args()->isNonEmpty())
        out << "(";
        
    prettyPrint(symb, out);
        
    TermList* args = term->args();
    while(args->isNonEmpty()) {
        out << " ";
        if(args->isVar())
            out << "x" << args->var();
        else
            prettyPrint(args->term(), out);
        args = args->next();
    }
        
    if(term->args()->isNonEmpty())
            out << ")";
}
    
/*print symbols in SMT*/
//TODO: use builtin enumerator for builtin operators instead of this trick...
//unfortunately I only discovered about those later..
void InterpolantMinimizer::prettyPrint(Symbol* symb, ostream& out)
{
    vstring name = symb->name();
    if(symb->interpreted()) {
        if(name == "$less")
        {out << "<";}
        else if(name == "$lesseq")
        {out << "<=";}
        else if(name == "$greater")
        {out << ">";}
        else if(name == "$greatereq")
        {out << ">=";}
        else if(name == "=")
        {out << "=";}
        else if(name == "$plus")
        {out << "+";}
        else if(name == "$sum")
        {out << "+";}
        else if(name == "$times")
        {out << "*";}
        else if(name == "$product")
        {out << "*";}
        else if(name == "$uminus")
        {out << "-";}
        else 
        {out << name;} //TODO: handle negative number and print them as (- N)
    }
    else{out<<name;}
}

    
    
    

/**
 * Into @c acc add all units that are sliced off in the model given
 * by SMT solver in @c solverResult.
 */
void InterpolantMinimizer::collectSlicedOffNodes(SMTSolverResult& solverResult, DHSet<Unit*>& acc)
{
  CALL("InterpolantMinimizer::collectSlicedOffNodes");

    
  InfoMap::Iterator uit(_infos);
  while(uit.hasNext()) {
    Unit* unit;
    UnitInfo info;
    uit.next(unit, info);

    if(info.color!=COLOR_TRANSPARENT || !info.leadsToColor) {
      continue;
    }

    vstring uid = getUnitId(unit);
    
    SMTConstant sU = pred(S, uid);
    vstring val = solverResult.assignment.get(sU);
    if(val=="false") {
      continue;
    }
    ASS_EQ(val,"true");
    acc.insert(unit);
  }

  TRACE(
  WeightMap::Iterator wit(_atomWeights);
  while(wit.hasNext()) {
    vstring atom;
    unsigned weight;
    wit.next(atom, weight);

    Unit* unit = _unitsById.get(atom);

    SMTConstant vU = pred(V, atom);

    cout << "because " << solverResult.assignment.get(vU) << " for " << unit->toString() << endl;
  })
}

/**
 * Add into @c _resBenchmark all formulas needed for interpolant minimization
 */
void InterpolantMinimizer::addAllFormulas()
{
  CALL("InterpolantMinimizer::addAllFormulas");

  InfoMap::Iterator uit(_infos);
  while(uit.hasNext()) {
    Unit* unit;
    UnitInfo info;
    uit.next(unit, info);

    if(info.color==COLOR_TRANSPARENT && info.leadsToColor) {
      addNodeFormulas(unit); 
    }
  }

  addCostFormula();
}

/**
 * Add into @c _resBenchmark formulas related to @c u and to it's relation to
 * its parents.
 */
void InterpolantMinimizer::addNodeFormulas(Unit* u)
{
  CALL("InterpolantMinimizer::addNodeFormulas");

  static ParentSummary psum;
  psum.reset();

  UnitIterator pit = InferenceStore::instance()->getParents(u);
  while(pit.hasNext()) {
    Unit* par = pit.next();
    UnitInfo& info = _infos.get(par);
    if(!info.leadsToColor) {
      continue;
    }
    vstring parId = getUnitId(par);
    switch(info.color) {
    case COLOR_LEFT: psum.rParents.push(parId); break;
    case COLOR_RIGHT: psum.bParents.push(parId); break;
    case COLOR_TRANSPARENT: psum.gParents.push(parId); break;
    default: ASSERTION_VIOLATION;
    }
  }

  UnitInfo& uinfo = _infos.get(u);
  ASS_EQ(uinfo.color, COLOR_TRANSPARENT);

  vstring uId = getUnitId(u);

  if(uinfo.inputInheritedColor!=COLOR_TRANSPARENT) {
    //if unit has an inherited color, it must be input unit and therefore
    //cannot have any parents
    ASS(psum.rParents.isEmpty());
    ASS(psum.bParents.isEmpty());
    ASS(psum.gParents.isEmpty());
    addLeafNodePropertiesFormula(uId);
  }
  else {
    addNodeFormulas(uId, psum);
    addFringeFormulas(u);
  }



  if(_noSlicing || uinfo.isRefutation) {
    vstring comment;
    if(uinfo.isRefutation) {
      comment += "refutation";
    }
    _resBenchmark.addFormula(!pred(S,uId), comment);
  }

  //if formula is a parent of colored formula, we do not allow to have
  //opposite color in the trace.
  if(uinfo.isParentOfLeft) {
    _resBenchmark.addFormula(!pred(B,uId), "parent_of_left");
  }
  if(uinfo.isParentOfRight) {
    _resBenchmark.addFormula(!pred(R,uId), "parent_of_right");
  }

  addAtomImplicationFormula(u);
}

/**
 * Add formulas related tot he fringe of the node and to the digest
 *
 * These formulas aren't generated for leaves
 */
void InterpolantMinimizer::addFringeFormulas(Unit* u)
{
  CALL("InterpolantMinimizer::addFringeFormulas");

  vstring n = getUnitId(u);

  SMTFormula rcN = pred(RC, n);
  SMTFormula bcN = pred(BC, n);
  SMTFormula rfN = pred(RF, n);
  SMTFormula bfN = pred(BF, n);
  SMTFormula dN = pred(D, n);

  _resBenchmark.addFormula(dN -=- ((rcN & !rfN) | (bcN & !bfN)));

  UnitInfo& uinfo = _infos.get(u);

  if(uinfo.isRefutation) {
    _resBenchmark.addFormula(!rfN);
    _resBenchmark.addFormula(bfN);
    return;
  }

  SMTFormula rfRhs = SMTFormula::getTrue();
  SMTFormula bfRhs = SMTFormula::getTrue();
  UList::Iterator gsit(uinfo.transparentSuccessors);
  while(gsit.hasNext()) {
    Unit* succ = gsit.next();
    vstring succId = getUnitId(succ);

    SMTFormula rcS = pred(RC, succId);
    SMTFormula bcS = pred(BC, succId);
    SMTFormula rfS = pred(RF, succId);
    SMTFormula bfS = pred(BF, succId);

    rfRhs = rfRhs & ( rfS | rcS ) & !bcS;
    bfRhs = bfRhs & ( bfS | bcS ) & !rcS;
  }


  if(uinfo.rightSuccessors) {
    _resBenchmark.addFormula(!rfN);
  }
  else {
    _resBenchmark.addFormula(rfN -=- rfRhs);
  }

  if(uinfo.leftSuccessors) {
    _resBenchmark.addFormula(!bfN);
  }
  else {
    _resBenchmark.addFormula(bfN -=- bfRhs);
  }

}

/////////////////////////////////////////////////////////
// Generating the weight-minimizing part of the problem
//

/**
 * Class that splits a clause into components, facilitating also
 * sharing of the components
 */
class InterpolantMinimizer::ClauseSplitter {
public:
  CLASS_NAME(InterpolantMinimizer::ClauseSplitter);
  USE_ALLOCATOR(InterpolantMinimizer::ClauseSplitter);

  ClauseSplitter() : _index(new SubstitutionTreeClauseVariantIndex()), _acc(0) {}
  
  /**
   * Into @c acc push clauses that correspond to components of @c cl.
   * The components are shared among calls to the function, so for
   * components that are variants of each other, the same result is
   * returned.
   */
  void getComponents(Clause* cl, ClauseStack& acc)
  {
    CALL("InterpolantMinimizer::ClauseSplitter::getComponents");
    ASS(!_acc);

    _acc = &acc;

    if(cl->length()==0) {
      handleNoSplit(cl);
    }
    else {
      doSplitting(cl);
    }

    _acc = 0;
  }
protected:

  void doSplitting(Clause* cl) {

    static Stack<LiteralStack> comps;
    comps.reset();
    // fills comps with components, returning if not splittable
    if(!Saturation::Splitter::getComponents(cl, comps)) {
      handleNoSplit(cl);
    } else {
      buildAndInsertComponents(comps.begin(),comps.size());
    }
  }

  void buildAndInsertComponents(const LiteralStack* comps, unsigned compCnt)
  {
    CALL("InterpolantMinimizer::ClauseSplitter::buildAndInsertComponents");

    for(unsigned i=0; i<compCnt; i++) {
      Clause* compCl = getComponent(comps[i].begin(), comps[i].size());
      _acc->push(compCl);
    }
  }  

  void handleNoSplit(Clause* cl)
  {
    CALL("InterpolantMinimizer::ClauseSplitter::handleNoSplit");

    _acc->push(getComponent(cl));
  }

private:

  Clause* getComponent(Literal* const * lits, unsigned len)
  {
    CALL("InterpolantMinimizer::ClauseSplitter::getComponent/2");

    if(len==1) {
      return getAtomComponent(lits[0], 0);
    }
    ClauseIterator cit = _index->retrieveVariants(lits, len);
    if(cit.hasNext()) {
      Clause* res = cit.next();
      ASS(!cit.hasNext());
      return res;
    }
    //here the input type and inference are just arbitrary, they'll never be used
    Clause* res = Clause::fromIterator(getArrayishObjectIterator(lits, len),NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
    res->incRefCnt();
    _index->insert(res);
    return res;
  }

  Clause* getComponent(Clause* cl)
  {
    CALL("InterpolantMinimizer::ClauseSplitter::getComponent/1");

    if(cl->length()==1) {
      return getAtomComponent((*cl)[0], cl);
    }

    ClauseIterator cit = _index->retrieveVariants(cl);
    if(cit.hasNext()) {
      Clause* res = cit.next();
      ASS(!cit.hasNext());
      return res;
    }
    _index->insert(cl);
    return cl;
  }

  /** cl can be 0 */
  Clause* getAtomComponent(Literal* lit, Clause* cl)
  {
    CALL("InterpolantMinimizer::ClauseSplitter::getAtomComponent");

    Literal* norm = Literal::positiveLiteral(lit);
    norm = Renaming::normalize(norm);

    Clause* res;
    if(_atomIndex.find(norm, res)) {
      return res;
    }
    res = cl;
    if(!res) {
      res = Clause::fromIterator(getSingletonIterator(norm),
          NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
    }
    ALWAYS(_atomIndex.insert(norm, res));
    return res;
  }

  ScopedPtr<ClauseVariantIndex> _index;
  DHMap<Literal*,Clause*> _atomIndex;

  ClauseStack* _acc;
};

/**
 * Into @c atoms add IDs of components that appear in FormulaUnit @c u
 *
 * Currently we consider formulas to be one big component.
 */
void InterpolantMinimizer::collectAtoms(FormulaUnit* f, Stack<vstring>& atoms)
{
  CALL("InterpolantMinimizer::collectAtoms(FormulaUnit*...)");
  
  vstring key = f->formula()->toString();

  vstring id;
  if(!_formulaAtomIds.find(key, id)) {
    id = "f" + Int::toString(_formulaAtomIds.size());
    _formulaAtomIds.insert(key, id);
    unsigned weight = f->formula()->weight();
    _atomWeights.insert(id, weight);
    _unitsById.insert(id, f);
  }
  
  atoms.push(id);
}

/**
 * Get ID of component @c cl
 */
vstring InterpolantMinimizer::getComponentId(Clause* cl)
{
  CALL("InterpolantMinimizer::getComponentId");
  vstring id;
  if(!_atomIds.find(cl, id)) {
    id = "c" + Int::toString(_atomIds.size());
    _atomIds.insert(cl, id);
    unsigned weight = cl->weight();
    _atomWeights.insert(id, weight);
    _unitsById.insert(id, cl);
  }
  return id;
}

/**
 * Into @c atoms add IDs of components that appear in @c u
 * If the formula is not a clause (i.e. conjunction of formulas), then the sub-formulas need to be traversed
 * (though currently, conjunctions of clauses is treated one formula in interpolation)
 */
void InterpolantMinimizer::collectAtoms(Unit* u, Stack<vstring>& atoms)
{
  CALL("InterpolantMinimizer::collectAtoms(Unit*...)");

  if(!u->isClause()) {
    collectAtoms(static_cast<FormulaUnit*>(u), atoms);
    return;
  }
  
  Clause* cl = u->asClause();
    
  static ClauseStack components;
  components.reset();
  _splitter->getComponents(cl, components);
  ASS(components.isNonEmpty());
  ClauseStack::Iterator cit(components);

  TRACE(cout << "collecting for " << u->toString() << endl);

  while(cit.hasNext()) {
    Clause* comp = cit.next();

    TRACE(cout << "comp " << comp->toString() << endl);

    atoms.push(getComponentId(comp));
  }
}

/**
 * Add formula implying the presence of components of @c u if
 * it appears in the digest into @c _resBenchmark
 */
void InterpolantMinimizer::addAtomImplicationFormula(Unit* u)
{
  CALL("InterpolantMinimizer::getAtomImplicationFormula");
  
  
  static Stack<vstring> atoms;
  atoms.reset();
  
  collectAtoms(u, atoms);

  vstring uId = getUnitId(u);

  SMTFormula cConj = SMTFormula::getTrue();
  Stack<vstring>::Iterator ait(atoms);
  while(ait.hasNext()) {
    
    vstring atom = ait.next();
    cConj = cConj & pred(V, atom);
  }

  vstring comment = "atom implications for " + u->toString();
  _resBenchmark.addFormula(pred(D, uId) --> cConj, comment);
}

/**
 * Add formula defining the cost function into @c _resBenchmark
 */
void InterpolantMinimizer::addCostFormula()
{
  CALL("InterpolantMinimizer::getCostFormula");

  TRACE(cout << "adding cost fla" << endl);

  SMTFormula costSum = SMTFormula::unsignedValue(0);

  WeightMap::Iterator wit(_atomWeights);
  while(wit.hasNext()) {
    vstring atom;
    unsigned weight;
    wit.next(atom, weight);

    Unit* unit = _unitsById.get(atom);
    unsigned varCnt = unit->varCnt();

    if(_optTarget==OT_COUNT && weight>0) {
      weight = 1;
    }
    //**minimize the interpolant wrt the number of quantifiers
    if(_optTarget==OT_QUANTIFIERS){
      weight = varCnt;
    }

    TRACE(cout << "cost " << weight << " for unit " << unit->toString() << endl);

    SMTFormula atomExpr = SMTFormula::condNumber(pred(V, atom), weight);
    costSum = SMTFormula::add(costSum, atomExpr);
  }
  _resBenchmark.addFormula(SMTFormula::equals(costFunction(), costSum));
}

///////////////////////////////////////////
// Generating the SAT part of the problem
//

SMTConstant InterpolantMinimizer::pred(PredType t, vstring node)
{
  CALL("InterpolantMinimizer::pred");
  //Fake node is fictitious parent of gray nodes marked as colored in the TPTP.
  //We should never create predicates for these.
  ASS_NEQ(node, "fake_node");

  vstring n1;
  switch(t) {
  case R: n1 = "r"; break;
  case B: n1 = "b"; break;
  case G: n1 = "g"; break;
  case S: n1 = "s"; break;
  case RC: n1 = "rc"; break;
  case BC: n1 = "bc"; break;
  case RF: n1 = "rf"; break;
  case BF: n1 = "bf"; break;
  case D: n1 = "d"; break;
  case V: n1 = "v"; break;
  default: ASSERTION_VIOLATION;
  }
  SMTConstant res = SMTFormula::name(n1, node);
  _resBenchmark.declarePropositionalConstant(res);
  return res;
}

SMTConstant InterpolantMinimizer::costFunction()
{
  SMTConstant res = SMTFormula::name("cost");
  _resBenchmark.declareRealConstant(res);
  return res;
}

vstring InterpolantMinimizer::getUnitId(Unit* u)
{
  CALL("InterpolantMinimizer::getUnitId");

  vstring id = InferenceStore::instance()->getUnitIdStr(u);
//  _idToFormulas.insert(is, u); //the item might be already there from previous call to getUnitId
  return id;
}

/**
 * Add into @c _resBenchmark formulas stating uniqueness of trace colours
 * of node @c n.
 */
void InterpolantMinimizer::addDistinctColorsFormula(vstring n)
{
  CALL("InterpolantMinimizer::distinctColorsFormula");

  SMTFormula rN = pred(R, n);
  SMTFormula bN = pred(B, n);
  SMTFormula gN = pred(G, n);

  SMTFormula res = bN | rN | gN;
  res = res & ( rN --> ((!bN) & (!gN)) );
  res = res & ( bN --> ((!rN) & (!gN)) );
  res = res & ( gN --> ((!rN) & (!bN)) );

  _resBenchmark.addFormula(res);
}

/**
 * Add into @c _resBenchmark formulas related to digest and trace of node @c n
 * that are specific to a node which is parent of only gray formulas.
 */
void InterpolantMinimizer::addGreyNodePropertiesFormula(vstring n, ParentSummary& parents)
{
  CALL("InterpolantMinimizer::gNodePropertiesFormula");
  ASS(parents.rParents.isEmpty());
  ASS(parents.bParents.isEmpty());

  SMTFormula rParDisj = SMTFormula::getFalse();
  SMTFormula bParDisj = SMTFormula::getFalse();
  SMTFormula gParConj = SMTFormula::getTrue();

  Stack<vstring>::Iterator pit(parents.gParents);
  while(pit.hasNext()) {
    vstring par = pit.next();
    rParDisj = rParDisj | pred(R, par);
    bParDisj = bParDisj | pred(B, par);
    gParConj = gParConj & pred(G, par);
  }

  SMTFormula rN = pred(R, n);
  SMTFormula bN = pred(B, n);
  SMTFormula gN = pred(G, n);
  SMTFormula sN = pred(S, n);
  SMTFormula rcN = pred(RC, n);
  SMTFormula bcN = pred(BC, n);
//  SMTFormula dN = pred(D, n);


  _resBenchmark.addFormula(rcN -=- ((!sN) & rParDisj));
  _resBenchmark.addFormula(bcN -=- ((!sN) & bParDisj));

  _resBenchmark.addFormula(rParDisj-->!bParDisj);
  _resBenchmark.addFormula(bParDisj-->!rParDisj);
  _resBenchmark.addFormula((sN & rParDisj)-->rN);
  _resBenchmark.addFormula((sN & bParDisj)-->bN);
  _resBenchmark.addFormula((sN & gParConj)-->gN);
  _resBenchmark.addFormula( (!sN)-->gN );
//  _resBenchmark.addFormula( dN -=- ( (!sN) & !gParConj ) );
}

/**
 * Add properties for a leaf node which was marked as colored in the TPTP problem,
 * but doesn't contain any colored symbols
 */
void InterpolantMinimizer::addLeafNodePropertiesFormula(vstring n)
{
  CALL("InterpolantMinimizer::addLeafNodePropertiesFormula");
 
    
  SMTFormula gN = pred(G, n);
  SMTFormula sN = pred(S, n);
  SMTFormula dN = pred(D, n);

  _resBenchmark.addFormula(!sN);
  _resBenchmark.addFormula(gN);
  _resBenchmark.addFormula(dN);
}

/**
 * Add into @c _resBenchmark formulas related to digest and trace of node @c n
 * that are specific to a node which is parent of a colored formula.
 */
void InterpolantMinimizer::addColoredParentPropertiesFormulas(vstring n, ParentSummary& parents)
{
  CALL("InterpolantMinimizer::coloredParentPropertiesFormula");
  ASS_NEQ(parents.rParents.isNonEmpty(),parents.bParents.isNonEmpty());

  PredType parentType = parents.rParents.isNonEmpty() ? R : B;
  PredType oppositeType = (parentType==R) ? B : R;

  Stack<vstring>::Iterator gParIt(parents.gParents);

  SMTFormula gParNegConj = SMTFormula::getTrue();
  while(gParIt.hasNext()) {
    vstring par = gParIt.next();
    gParNegConj = gParNegConj & !pred(oppositeType, par);
  }

  SMTFormula parN = pred(parentType, n);
  SMTFormula gN = pred(G, n);
  SMTFormula sN = pred(S, n);
  SMTFormula rcN = pred(RC, n);
  SMTFormula bcN = pred(BC, n);
//  SMTFormula dN = pred(D, n);

  if(parentType==R) {
    _resBenchmark.addFormula(rcN -=- !sN);
    _resBenchmark.addFormula(!bcN);
  }
  else {
    ASS_EQ(parentType,B);
    _resBenchmark.addFormula(bcN -=- !sN);
    _resBenchmark.addFormula(!rcN);
  }

  _resBenchmark.addFormula(gParNegConj);
  _resBenchmark.addFormula(sN --> parN);
  _resBenchmark.addFormula((!sN) --> gN);
//  _resBenchmark.addFormula(dN -=- !sN);
}

/**
 * Add into @c _resBenchmark formulas related to digest and trace of node @c n, provided
 * @c n is not a leaf node.
 *
 * Formulas related to the cost function are added elsewhere.
 */
void InterpolantMinimizer::addNodeFormulas(vstring n, ParentSummary& parents)
{
  CALL("InterpolantMinimizer::propertiesFormula");

  addDistinctColorsFormula(n);

  if(parents.rParents.isEmpty() && parents.bParents.isEmpty()) {
    addGreyNodePropertiesFormula(n, parents);
  }
  else {
    addColoredParentPropertiesFormulas(n, parents);
  }
}

/////////////////////////
// Proof tree traversal
//

struct InterpolantMinimizer::TraverseStackEntry
{
  TraverseStackEntry(InterpolantMinimizer& im, Unit* u) : unit(u), _im(im)
  {
    CALL("InterpolantMinimizer::TraverseStackEntry::TraverseStackEntry");

    parentIterator = InferenceStore::instance()->getParents(u);

    //we don't create stack entries for already visited units,
    //so we must always be able to insert
    ALWAYS(im._infos.insert(unit, UnitInfo()));
    UnitInfo& info = getInfo();

    info.color = u->getColor();
    info.inputInheritedColor = u->inheritedColor();
    if(info.inputInheritedColor==COLOR_INVALID) {
      if(!parentIterator.hasNext()) {
	//this covers introduced name definitions
	info.inputInheritedColor = info.color;
      }
      else {
	info.inputInheritedColor = COLOR_TRANSPARENT;
      }
    }

    info.leadsToColor = info.color!=COLOR_TRANSPARENT || info.inputInheritedColor!=COLOR_TRANSPARENT;
  }

  /**
   * Extract the needed information on the relation between the current unit
   * and its premise @c parent
   */
  void processParent(Unit* parent)
  {
    CALL("InterpolantMinimizer::TraverseStackEntry::processParent");

    UnitInfo& info = getInfo();

    UnitInfo& parInfo = _im._infos.get(parent);
//    Color pcol = parent.unit()->getColor();
    Color pcol = parInfo.color;
    if(pcol==COLOR_LEFT) {
      ASS_NEQ(info.state, HAS_RIGHT_PARENT);
      info.state = HAS_LEFT_PARENT;
    }
    if(pcol==COLOR_RIGHT) {
      ASS_REP2(info.state!=HAS_LEFT_PARENT, unit->toString(), parent->toString());
      info.state = HAS_RIGHT_PARENT;
    }

    info.leadsToColor |= parInfo.leadsToColor;

    if(info.color==COLOR_LEFT) {
      parInfo.isParentOfLeft = true;
      UList::push(unit, parInfo.leftSuccessors);
    }
    else if(info.color==COLOR_RIGHT) {
      parInfo.isParentOfRight = true;
      UList::push(unit, parInfo.rightSuccessors);
    }
    else {
      ASS_EQ(info.color, COLOR_TRANSPARENT);
      UList::push(unit, parInfo.transparentSuccessors);
    }
  }

  /**
   * The returned reference is valid only before updating
   * InterpolantMinimizer::_infos
   */
  UnitInfo& getInfo()
  {
    return _im._infos.get(unit);
  }

  Unit* unit;
  /** Premises that are yet to be traversed */
  UnitIterator parentIterator;

  InterpolantMinimizer& _im;
};

/**
 * Traverse through the proof graph of @c refutationClause and
 * record everything that is necessary for generating the
 * minimization problem
 */
void InterpolantMinimizer::traverse(Unit* refutationUnit)
{
  CALL("InterpolantMinimizer::traverse");

  Unit* refutation = refutationUnit;

  static Stack<TraverseStackEntry> stack;
  stack.reset();

  stack.push(TraverseStackEntry(*this, refutation));
  stack.top().getInfo().isRefutation = true;
  while(stack.isNonEmpty()) {
    TraverseStackEntry& top = stack.top();
    if(top.parentIterator.hasNext()) {
      Unit* parent = top.parentIterator.next();

      if(!_infos.find(parent)) {
	stack.push(TraverseStackEntry(*this, parent));
      }
      else {
	top.processParent(parent);
      }
    }
    else {
      if(stack.size()>1){
	TraverseStackEntry& child = stack[stack.size()-2];
	child.processParent(stack.top().unit);
      }
      stack.pop();
    }
  }

}

/**
 * Create InterpolantMinimizer object
 *
 * @param target optimiziation target, determines what should be optimised.
 *
 * @param noSlicing If true, we forbid all slicing of proof nodes. This simulates
 * the original algorithm which didn't use minimization.
 *
 * @param showStats Value of the cost function is output
 *
 * @param statsPrefix The value of the cost function is output on line starting
 * with statsPrefix + " cost: "
 */
InterpolantMinimizer::InterpolantMinimizer(OptimizationTarget target, bool noSlicing,
					   bool showStats, vstring statsPrefix)
  : _optTarget(target),
    _noSlicing(noSlicing),
    _showStats(showStats),
    _statsPrefix(statsPrefix)
{
  CALL("InterpolantMinimizer::InterpolantMinimizer");

  _splitter = new ClauseSplitter();
}

InterpolantMinimizer::~InterpolantMinimizer()
{
  CALL("InterpolantMinimizer::~InterpolantMinimizer");

  delete _splitter;
}
