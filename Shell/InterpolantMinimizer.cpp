/**
 * @file InterpolantMinimizer
 * Implements class InterpolantMinimizer.
 */

#include <fstream>
#include <sstream>

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"

#include "Interpolants.hpp"
#include "Options.hpp"

#include "InterpolantMinimizer.hpp"

namespace Shell
{

Formula* InterpolantMinimizer::getInterpolant(Clause* refutation)
{
  CALL("InterpolantMinimizer::getInterpolant");

  _noSlicing = false;
//  _noSlicing = true;

  traverse(refutation);
  addAllFormulas();

  SMTSolverResult res;
  YicesSolver solver;
  solver.minimize(_resBenchmark, costFunction(), res);
//  LOGV(res.assignment.get(costFunction()));

  DHSet<UnitSpec> slicedOff;
  collectSlicedOffNodes(res, slicedOff);

  Formula* interpolant = Interpolants(&slicedOff).getInterpolant(refutation);
  return interpolant;
}

void InterpolantMinimizer::collectSlicedOffNodes(SMTSolverResult& solverResult, DHSet<UnitSpec>& acc)
{
  CALL("InterpolantMinimizer::collectSlicedOffNodes");

  InfoMap::Iterator uit(_infos);
  while(uit.hasNext()) {
    UnitSpec unit;
    UnitInfo info;
    uit.next(unit, info);

    if(info.color!=COLOR_TRANSPARENT || !info.leadsToColor) {
      continue;
    }

    string uid = getUnitId(unit);
    SMTConstant sU = pred(S, uid);
    string val = solverResult.assignment.get(sU);
    if(val=="false") {
      continue;
    }
    ASS_EQ(val,"true");
    acc.insert(unit);
//    LOGV(unit.toString());
  }
}

void InterpolantMinimizer::addAllFormulas()
{
  CALL("InterpolantMinimizer::getWholeFormula");

  InfoMap::Iterator uit(_infos);
  while(uit.hasNext()) {
    UnitSpec unit;
    UnitInfo info;
    uit.next(unit, info);

    if(info.color==COLOR_TRANSPARENT && info.leadsToColor) {
      addNodeFormulas(unit);
    }
  }

  addCostFormula();
}

void InterpolantMinimizer::addNodeFormulas(UnitSpec u)
{
  CALL("InterpolantMinimizer::getNodeFormula");

  static ParentSummary psum;
  psum.reset();

  VirtualIterator<UnitSpec> pit = InferenceStore::instance()->getParents(u);
  while(pit.hasNext()) {
    UnitSpec par = pit.next();
    UnitInfo& info = _infos.get(par);
    if(!info.leadsToColor) {
      continue;
    }
    string parId = getUnitId(par);
    switch(info.color) {
    case COLOR_LEFT: psum.rParents.push(parId); break;
    case COLOR_RIGHT: psum.bParents.push(parId); break;
    case COLOR_TRANSPARENT: psum.gParents.push(parId); break;
    default: ASSERTION_VIOLATION;
    }
  }

  string uId = getUnitId(u);
  addNodeFormulas(uId, psum);

  UnitInfo& uinfo = _infos.get(u);

  if(_noSlicing || uinfo.isRefutation) {
    string comment;
    if(uinfo.isRefutation) {
      comment += "refutation";
    }
    _resBenchmark.addFormula(!pred(S,uId), comment);
  }

  //if formula is a parent of colored formula, we do not allow to slice it,
  //if it would have opposite color in the digest.
  if(uinfo.isParentOfLeft) {
    _resBenchmark.addFormula(!pred(B,uId), "parent_of_left");
  }
  if(uinfo.isParentOfRight) {
    _resBenchmark.addFormula(!pred(R,uId), "parent_of_right");
  }

  addAtomImplicationFormula(u);
}


/////////////////////////////////////////////////////////
// Generating the weight-minimizing part of the problem
//

void InterpolantMinimizer::collectAtoms(FormulaUnit* f, Stack<string>& atoms)
{
  CALL("InterpolantMinimizer::collectAtoms(FormulaUnit*...)");

  string key = f->formula()->toString();
  string id;
  if(!_formulaAtomIds.find(key, id)) {
    id = "f" + Int::toString(_formulaAtomIds.size());
    _formulaAtomIds.insert(key, id);
    unsigned weight = key.size();
    _atomWeights.insert(id, weight);
  }
  atoms.push(id);
}

string InterpolantMinimizer::getLiteralId(Literal* l)
{
  CALL("InterpolantMinimizer::getLiteralId");

  Literal* key = l->isNegative() ? Literal::oppositeLiteral(l) : l;
  string id;
  if(!_atomIds.find(key, id)) {
    id = "l" + Int::toString(_atomIds.size());
    _atomIds.insert(key, id);
    unsigned weight = key->weight();
    _atomWeights.insert(id, weight);
  }
 return id;
}

void InterpolantMinimizer::collectAtoms(UnitSpec u, Stack<string>& atoms)
{
  CALL("InterpolantMinimizer::collectAtoms(UnitSpec...)");

  if(!u.isClause()) {
    collectAtoms(static_cast<FormulaUnit*>(u.unit()), atoms);
    return;
  }

  Clause* cl = u.cl();
  Clause::Iterator cit(*cl);
  while(cit.hasNext()) {
    Literal* lit = cit.next();
    atoms.push(getLiteralId(lit));
  }
}

void InterpolantMinimizer::addAtomImplicationFormula(UnitSpec u)
{
  CALL("InterpolantMinimizer::getAtomImplicationFormula");

  static Stack<string> atoms;
  atoms.reset();
  collectAtoms(u, atoms);

  string uId = getUnitId(u);

  SMTFormula cConj = SMTFormula::getTrue();
  Stack<string>::Iterator ait(atoms);
  while(ait.hasNext()) {
    string atom = ait.next();
    cConj = cConj & pred(V, atom);
  }

  string comment = "atom implications for " + u.toString();
  _resBenchmark.addFormula(pred(D, uId) --> cConj, comment);
}

void InterpolantMinimizer::addCostFormula()
{
  CALL("InterpolantMinimizer::getCostFormula");

  SMTFormula costSum = SMTFormula::unsignedValue(0);

  WeightMap::Iterator wit(_atomWeights);
  while(wit.hasNext()) {
    string atom;
    unsigned weight;
    wit.next(atom, weight);

    SMTFormula atomExpr = SMTFormula::condNumber(pred(V, atom), weight);
    costSum = SMTFormula::add(costSum, atomExpr);
  }
  _resBenchmark.addFormula(SMTFormula::equals(costFunction(), costSum));
}

///////////////////////////////////////////
// Generating the SAT part of the problem
//

SMTConstant InterpolantMinimizer::pred(PredType t, string node)
{
  CALL("InterpolantMinimizer::pred");

  string n1;
  switch(t) {
  case R: n1 = "r"; break;
  case B: n1 = "b"; break;
  case G: n1 = "g"; break;
  case S: n1 = "s"; break;
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

string InterpolantMinimizer::getUnitId(UnitSpec u)
{
  CALL("InterpolantMinimizer::getUnitId");

  string id = InferenceStore::instance()->getUnitIdStr(u);
//  _idToFormulas.insert(is, u); //the item might be already there from previous call to getUnitId
  return id;
}

void InterpolantMinimizer::addDistinctColorsFormula(string n)
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

void InterpolantMinimizer::addGreyNodePropertiesFormula(string n, ParentSummary& parents)
{
  CALL("InterpolantMinimizer::gNodePropertiesFormula");
  ASS(parents.rParents.isEmpty());
  ASS(parents.bParents.isEmpty());

  SMTFormula rParDisj = SMTFormula::getFalse();
  SMTFormula bParDisj = SMTFormula::getFalse();
  SMTFormula gParConj = SMTFormula::getTrue();

  Stack<string>::Iterator pit(parents.gParents);
  while(pit.hasNext()) {
    string par = pit.next();
    rParDisj = rParDisj | pred(R, par);
    bParDisj = bParDisj | pred(B, par);
    gParConj = gParConj & pred(G, par);
  }

  SMTFormula rN = pred(R, n);
  SMTFormula bN = pred(B, n);
  SMTFormula gN = pred(G, n);
  SMTFormula sN = pred(S, n);
  SMTFormula dN = pred(D, n);

  _resBenchmark.addFormula(rParDisj-->!bParDisj);
  _resBenchmark.addFormula(bParDisj-->!rParDisj);
  _resBenchmark.addFormula((sN & rParDisj)-->rN);
  _resBenchmark.addFormula((sN & bParDisj)-->bN);
  _resBenchmark.addFormula((sN & gParConj)-->gN);
  _resBenchmark.addFormula( (!sN)-->gN );
  _resBenchmark.addFormula( dN -=- ( (!sN) & !gParConj ) );
}

void InterpolantMinimizer::addColoredParentPropertiesFormulas(string n, ParentSummary& parents)
{
  CALL("InterpolantMinimizer::coloredParentPropertiesFormula");
  ASS_NEQ(parents.rParents.isNonEmpty(),parents.bParents.isNonEmpty());

  PredType parentType = parents.rParents.isNonEmpty() ? R : B;
  PredType oppositeType = (parentType==R) ? B : R;

  Stack<string>::Iterator gParIt(parents.gParents);

  SMTFormula gParNegConj = SMTFormula::getTrue();
  while(gParIt.hasNext()) {
    string par = gParIt.next();
    gParNegConj = gParNegConj & !pred(oppositeType, par);
  }

  SMTFormula parN = pred(parentType, n);
  SMTFormula gN = pred(G, n);
  SMTFormula sN = pred(S, n);
  SMTFormula dN = pred(D, n);

  _resBenchmark.addFormula(gParNegConj);
  _resBenchmark.addFormula(sN --> parN);
  _resBenchmark.addFormula((!sN) --> gN);
  _resBenchmark.addFormula(dN -=- !sN);
}

void InterpolantMinimizer::addNodeFormulas(string n, ParentSummary& parents)
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
  TraverseStackEntry(InterpolantMinimizer& im, UnitSpec u) : unit(u), _im(im)
  {
    CALL("InterpolantMinimizer::TraverseStackEntry::TraverseStackEntry");

    parentIterator = InferenceStore::instance()->getParents(u);

    //we don't create stack entries for already visited units,
    //so we must always be able to insert
    ALWAYS(im._infos.insert(unit, UnitInfo()));
    UnitInfo& info = getInfo();

    info.color = u.unit()->getColor();
    info.leadsToColor = info.color!=COLOR_TRANSPARENT;
  }

  void processParent(UnitSpec parent)
  {
    CALL("InterpolantMinimizer::TraverseStackEntry::processParent");

    UnitInfo& info = getInfo();

    Color pcol = parent.unit()->getColor();
    if(pcol==COLOR_LEFT) {
      ASS_NEQ(info.state, HAS_RIGHT_PARENT);
      info.state = HAS_LEFT_PARENT;
    }
    if(pcol==COLOR_RIGHT) {
      ASS_NEQ(info.state, HAS_LEFT_PARENT);
      info.state = HAS_RIGHT_PARENT;
    }

    UnitInfo& parInfo = _im._infos.get(parent);
    info.leadsToColor |= parInfo.leadsToColor;

    if(info.color==COLOR_LEFT) {
      parInfo.isParentOfLeft = true;
    }
    if(info.color==COLOR_RIGHT) {
      parInfo.isParentOfRight = true;
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

  UnitSpec unit;
  VirtualIterator<UnitSpec> parentIterator;

  InterpolantMinimizer& _im;
};

void InterpolantMinimizer::traverse(Clause* refutationClause)
{
  CALL("InterpolantMinimizer::traverse");

  UnitSpec refutation=UnitSpec(refutationClause, refutationClause->prop());

  static Stack<TraverseStackEntry> stack;
  stack.reset();

  stack.push(TraverseStackEntry(*this, refutation));
  stack.top().getInfo().isRefutation = true;
  while(stack.isNonEmpty()) {
    TraverseStackEntry& top = stack.top();
    if(top.parentIterator.hasNext()) {
      UnitSpec parent = top.parentIterator.next();

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



}
