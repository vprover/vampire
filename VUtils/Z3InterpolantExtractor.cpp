/**
 * @file Z3InterpolantExtractor.cpp
 * Implements class Z3InterpolantExtractor.
 */

#include <iostream>

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/InterpolantMinimizer.hpp"
#include "Shell/LispLexer.hpp"
#include "Shell/TPTP.hpp"


#include "LocalityRestoring.hpp"
#include "RangeColoring.hpp"

#include "Z3InterpolantExtractor.hpp"

namespace VUtils
{

///////////////////////
// proof extraction
//

string ZIE::hypothesesToString(List<TermList>* hypotheses)
{
  string res;
  List<TermList>::Iterator hit(hypotheses);
  while(hit.hasNext()) {
    TermList hyp = hit.next();
    res += hyp.toString();
    if(hit.hasNext()) {
	res += ", ";
    }
  }
  return res;
}

LExpr* ZIE::getInput()
{
  CALL("ZIE::getInput");

  LispLexer lex(cin);
  LispParser parser(lex);
  return parser.parse();
}

void print(LExpr* expr)
{
  if(expr->tag==LispParser::ATOM) {
    cout << expr->str;
    return;
  }
  cout << "(";
  LExprList::Iterator args(expr->list);
  while(args.hasNext()) {
    LExpr* arg = args.next();
    print(arg);
    if(args.hasNext()) {
      cout << " ";
    }
  }
  cout << ")";
}

void LISP_ERROR(string error, LExpr* expr)
{
  cout << "ERROR: "<< error << endl;
  print(expr);
  cout << endl;
  USER_ERROR("Lisp error");
}

bool ZIE::readLet(LExpr* expr, LExpr*& tail)
{
  CALL("ZIE::readLet");

  if(!expr->isList()) {
    return false;
  }

  LExpr* asgns;
  if(!expr->get2Args("let", asgns, tail)) {
    return false;
  }
  if(!asgns->isList()) { LISP_ERROR("let assignment is not a list", expr); }

  LExprList::Iterator asIt(asgns->list);
  while(asIt.hasNext()) {
    LExpr* asgn = asIt.next();
    LExpr* nameE;
    LExpr* value;
    if(!asgn->getPair(nameE, value)) { LISP_ERROR("invalid let assignment", asgn); }
    if(!nameE->isAtom()) { LISP_ERROR("invalid let assignment name", asgn); }
    string name = nameE->str;
    _letRecords.push(LetRecord(name, value));

//    LOG("let: " << name << " --> " << value->toString());
  }
  return true;
}

TermList ZIE::getTermAssignment(string name)
{
  CALL("ZIE::getTermAssignment");

  if(!_termAssignments.find(name)) {
    USER_ERROR("unassigned variable "+name);
  }
  return _termAssignments.get(name);
}

ZIE::ProofObject ZIE::getProofObjectAssignment(string name)
{
  CALL("ZIE::getProofObjectAssignment");

  if(!_proofAssignments.find(name)) {
    USER_ERROR("unassigned variable "+name);
  }
  return _proofAssignments.get(name);
}

TermList ZIE::negate(TermList term)
{
  CALL("ZIE::negate");

  unsigned notPred = env.signature->addFunction("not", 1);

  if(term.isTerm() && term.term()->functor()==notPred) {
    return *term.term()->nthArgument(0);
  }
  Term* negTrm = Term::create(notPred, 1, &term);
  return TermList(negTrm);
}

bool ZIE::tryReadNumber(LExpr* expr, TermList& res)
{
  CALL("ZIE::tryReadNumber");

  InterpretedType num;

  if(expr->isAtom() && Int::stringToInt(expr->str, num)) {
    unsigned func = env.signature->addInterpretedConstant(num);
    res = TermList(Term::create(func, 0, 0));
    return true;
  }

  LExpr* uminusArg;
  if(expr->get1Arg("-", uminusArg) || expr->get1Arg("~", uminusArg)) {
    if(uminusArg->isAtom() && Int::stringToInt(uminusArg->str, num) && Int::safeUnaryMinus(num, num)) {
      unsigned func = env.signature->addInterpretedConstant(num);
      res = TermList(Term::create(func, 0, 0));
      return true;
    }
  }

  return false;
}


TermList ZIE::readTerm(LExpr* term)
{
  CALL("ZIE::readTerm");

  {
    TermList numRes;
    if(tryReadNumber(term, numRes)) {
      return numRes;
    }
  }

  if(term->isAtom()) {
    //we have a constant or a let variable
    string name = term->str;

    if(isProofVariable(name)) { LISP_ERROR("proof variable inside term", term); }
    if(isTermVariable(name)) {
      return getTermAssignment(name);
    }

    unsigned func = env.signature->addFunction(name, 0);
    Term* trm = Term::create(func, 0, 0);
    return TermList(trm);
  }

  LExpr* unaryArg;
  if(term->get1Arg("not", unaryArg)) {
    TermList argTrm = readTerm(unaryArg);
    return negate(argTrm);
  }

  LExprList::Iterator args(term->list);
  if(!args.hasNext()) { LISP_ERROR("invalid term", term); }
  LExpr* nameE = args.next();
  if(!nameE->isAtom()) { LISP_ERROR("invalid term name", nameE); }
  string name = nameE->str;

  TermStack argStack;
  argStack.reset();
  while(args.hasNext()) {
    LExpr* argE = args.next();
    TermList arg = readTerm(argE);
    argStack.push(arg);
  }

  unsigned arity = argStack.size();
  unsigned func = env.signature->addFunction(name, arity);
  Term* trm = Term::create(func, arity, argStack.begin());
  TermList res(trm);
  onFunctionApplication(res);
  return res;
}

Formula* ZIE::termToFormula(TermList trm)
{
  CALL("ZIE::termToFormula/1");

  static unsigned pred = env.signature->addPredicate("e", 1);

  Literal* resLit = Literal::create(pred, 1, true, false, &trm);
  return new AtomicFormula(resLit);
}

Formula* ZIE::termToFormula(TermList trm, List<TermList>* hypotheses)
{
  CALL("ZIE::termToFormula/2");

  Formula* res = termToFormula(trm);

  if(hypotheses) {
    FormulaList* hypotheseForms = 0;
    List<TermList>::Iterator hit(hypotheses);
    while(hit.hasNext()) {
      TermList hypTrm = hit.next();
      Formula* hypForm = termToFormula(hypTrm);
      FormulaList::push(hypForm, hypotheseForms);
    }

    Formula* hypotheseForm;
    if(hypotheses->tail()) {
      hypotheseForm = new JunctionFormula(AND, hypotheseForms);
    }
    else {
      hypotheseForm = FormulaList::pop(hypotheseForms);
      ASS(!hypotheseForms);
    }
    res = new BinaryFormula(IMP, hypotheseForm, res);
  }
  return res;
}

void ZIE::resolveHypotheses(List<TermList>*& hypotheses, TermList lemma)
{
  CALL("ZIE::resolveHypotheses");

  {
    TermList hyp = negate(lemma);
    if(hypotheses->member(hyp)) {
      //this is the easy case when he have just one hypothesis to resolve
      hypotheses = hypotheses->remove(hyp);
      return;
    }
  }

  if(lemma.isTerm() && lemma.term()->functionName()=="or") {
    bool anyMissing = false;
    Term* lemmaT = lemma.term();
    unsigned disjArity = lemmaT->arity();
    for(unsigned i=0; i<disjArity; i++) {
      TermList subLemma = *lemmaT->nthArgument(i);
      TermList hyp = negate(subLemma);
      if(!hypotheses->member(hyp)) {
	anyMissing = true;
      }
    }
    if(!anyMissing) {
      for(unsigned i=0; i<disjArity; i++) {
        TermList subLemma = *lemmaT->nthArgument(i);
        TermList hyp = negate(subLemma);
        hypotheses = hypotheses->remove(hyp);
      }
      return;
    }
  }

  USER_ERROR("unable to resolve lemma with hypotheses\n"
	"hypotheses are "+hypothesesToString(hypotheses)+"\n"
	"we want to resolve "+lemma.toString());

}

ZIE::ProofObject ZIE::readProofObject(LExpr* expr)
{
  CALL("ZIE::readProofObject");

  if(expr->isAtom()) {
    //we have a constant or a let variable
    string name = expr->str;

    if(isTermVariable(name)) { LISP_ERROR("proof variable expected, term variable found", expr); }
    if(isProofVariable(name)) {
      return getProofObjectAssignment(name);
    }
    LOGS(name);
    LISP_ERROR("invalid proof object (neither list nor variable)", expr);
  }

  {
    LExpr* unaryArg;
    if(expr->get1Arg("hypothesis", unaryArg)) {
      TermList hyp = readTerm(unaryArg);
      List<TermList>* hypLst = 0;
      List<TermList>::push(hyp, hypLst);
      return ProofObject(0, hypLst);
    }
  }

  {
    LExpr* lemmaPrem;
    LExpr* lemmaHypNeg;
    if(expr->get2Args("lemma", lemmaPrem, lemmaHypNeg)) {
      ProofObject prem = readProofObject(lemmaPrem);
      TermList lemmaTrm = readTerm(lemmaHypNeg);

      if(!prem.unit) {
	LISP_ERROR("invalid lemma premise", expr);
      }

      List<TermList>* remainingHyp = prem.hypotheses->copy();
      resolveHypotheses(remainingHyp, lemmaTrm);

      Inference* inf = new Inference1(Inference::EXTERNAL, prem.unit);
      Formula* lemma = termToFormula(lemmaTrm, remainingHyp);
      FormulaUnit* lemmaUnit = new FormulaUnit(lemma, inf, Unit::AXIOM);

      _allUnits.push(lemmaUnit);
      return ProofObject(lemmaUnit, remainingHyp);
    }
  }

  {
    LExpr* monPremise;
    LExpr* monConclusion;
    if(expr->get2Args("monotonicity", monPremise, monConclusion)) {
      //we skip monotonicity inferences;
      return readProofObject(monPremise);
    }
  }


  LExprList::Iterator args(expr->list);
  if(!args.hasNext()) { LISP_ERROR("invalid proof object", expr); }
  LExpr* nameE = args.next();
  string name = nameE->toString();

  Stack<LExpr*> argStack;
  argStack.reset();
  while(args.hasNext()) {
    LExpr* arg = args.next();
    argStack.push(arg);
  }

  LExpr* conclusionExp = argStack.pop();
  TermList conclusionTrm = readTerm(conclusionExp);


  DHSet<TermList> hypotheseSet;
  hypotheseSet.reset();
  List<TermList>* hypotheseTerms = 0;
  UnitList* premises = 0;

  Stack<LExpr*>::BottomFirstIterator premExprIt(argStack);
  while(premExprIt.hasNext()) {
    LExpr* premExp = premExprIt.next();

    ProofObject po = readProofObject(premExp);
    if(po.unit) {
      UnitList::push(po.unit, premises);
    }
    List<TermList>::Iterator hit(po.hypotheses);
    while(hit.hasNext()) {
      TermList hypTrm = hit.next();
      if(!hypotheseSet.insert(hypTrm)) {
	continue;
      }
      List<TermList>::push(hypTrm, hypotheseTerms);
    }
  }

  Formula* conclusion = termToFormula(conclusionTrm, hypotheseTerms);

  bool input = false;
  Inference* inf;
  if(name=="asserted") {
    if(premises) { LISP_ERROR("asserted cannot have any premises", expr); }
    inf = new Inference(Inference::INPUT);
    input = true;
  }
  else {
    inf = new InferenceMany(Inference::EXTERNAL, premises);
  }
  FormulaUnit* resUnit = new FormulaUnit(conclusion, inf, Unit::AXIOM);
  if(input) {
    _inputUnits.push(resUnit);
  }
  _allUnits.push(resUnit);

  return ProofObject(resUnit, hypotheseTerms);
}

void ZIE::processLets()
{
  CALL("ZIE::processLets");

  Stack<LetRecord>::BottomFirstIterator letIt(_letRecords);
  while(letIt.hasNext()) {
    LetRecord lrec = letIt.next();
    string varName = lrec.first;
    LExpr* expr = lrec.second;
    if(isTermVariable(varName)) {
      TermList trm = readTerm(expr);
//      LOG(varName << " = " << trm.toString());
      if(!_termAssignments.insert(varName, trm)) {
	USER_ERROR("duplicate variable: " + varName);
      }
    }
    else if(isProofVariable(varName)) {
      ProofObject po = readProofObject(expr);
//      LOG(varName << " = " << (po.unit ? po.unit->toString() : "<hypothesis>"));
      if(!_proofAssignments.insert(varName, po)) {
	USER_ERROR("duplicate variable: " + varName);
      }
    }
    else {
      USER_ERROR("variable expected: "+varName);
    }

  }
}

///////////////////////
// coloring
//

ZIE::UnaryFunctionInfo::UnaryFunctionInfo(TermList firstArg)
{
  CALL("ZIE::UnaryFunctionInfo::UnaryFunctionInfo");

  numericArgsOnly = theory->isInterpretedConstant(firstArg);

  if(numericArgsOnly) {
    InterpretedType argVal = theory->interpretConstant(firstArg);
    minArg = maxArg = argVal;
  }
}

void ZIE::UnaryFunctionInfo::onNewArg(TermList firstArg)
{
  CALL("ZIE::UnaryFunctionInfo::onNewArg");

  if(!numericArgsOnly) {
    return;
  }

  bool isNumeric = theory->isInterpretedConstant(firstArg);
  if(isNumeric) {
    InterpretedType argVal = theory->interpretConstant(firstArg);
    if(argVal>maxArg) { maxArg = argVal; }
    if(argVal<minArg) { minArg = argVal; }
  }
  else {
    numericArgsOnly = false;
  }
}

void ZIE::onFunctionApplication(TermList fn)
{
  CALL("ZIE::onFunctionApplication");
  ASS(fn.isTerm());

  Term* t = fn.term();
  if(t->arity()!=1) { return; }
  unsigned func = t->functor();
  TermList arg = *t->nthArgument(0);
  UnaryFunctionInfo* pInfo;
  if(_unaryFnInfos.getValuePtr(func, pInfo)) {
    *pInfo = UnaryFunctionInfo(arg);
  }
  else {
    pInfo->onNewArg(arg);
  }
}

bool ZIE::colorProof(UnitStack& derivation, UnitStack& coloredDerivationTgt)
{
  CALL("ZIE::colorProof");

  bool first = true;

  RangeColoring rcol;

  InterpretedType globalMin;
  InterpretedType globalMax;

  UnaryInfoMap::Iterator uiit(_unaryFnInfos);
  while(uiit.hasNext()) {
    UnaryFunctionInfo uinfo;
    unsigned func;
    uiit.next(func, uinfo);
    if(!uinfo.numericArgsOnly) { continue; }

    if(first || globalMin>uinfo.minArg) {
      globalMin = uinfo.minArg;
    }
    if(first || globalMax<uinfo.maxArg) {
      globalMax = uinfo.maxArg;
    }
//    LOG(env.signature->functionName(func) << ": " << uinfo.minArg << ", " << uinfo.maxArg);
    rcol.addFunction(func);
  }
  InterpretedType midpoint = (globalMax+globalMin)/2;
  LOGV(midpoint);
  rcol.setMiddleValue(midpoint);

  if(!rcol.areUnitsLocal(_inputUnits)) {
    return false;
  }

  rcol.applyToDerivation(derivation, coloredDerivationTgt);

  return true;
}


///////////////////////
// main
//

Unit* ZIE::getZ3Refutation()
{
  CALL("ZIE::getZ3Refutation");

  env.colorUsed = true;

  LExpr* inp = getInput();

  LExpr* proofExpr;
  if(!inp->getSingleton(proofExpr)) { LISP_ERROR("invalid proof", inp); }

  while(readLet(proofExpr, proofExpr)) {}

  processLets();

  ProofObject pobj = readProofObject(proofExpr);
  if(pobj.hypotheses) {
    USER_ERROR("unresolved hypotheses: " + pobj.hypothesesToString());
  }
  return pobj.unit;
}

void ZIE::outputInterpolantStats(Unit* refutation)
{
  CALL("ZIE::outputInterpolantStats");

  Formula* oldInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, true, true, "Original interpolant weight").getInterpolant(refutation);
  Formula* interpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, false, true, "Minimized interpolant weight").getInterpolant(refutation);
  InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, true, true, "Original interpolant count").getInterpolant(refutation);
  Formula* cntInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, false, true, "Minimized interpolant count").getInterpolant(refutation);
  InterpolantMinimizer(InterpolantMinimizer::OT_QUANTIFIERS, true, true, "Original interpolant quantifiers").getInterpolant(refutation);
  Formula* quantInterpolant =  InterpolantMinimizer(InterpolantMinimizer::OT_QUANTIFIERS, false, true, "Minimized interpolant quantifiers").getInterpolant(refutation);

  cout << "Old interpolant: " << TPTP::toString(oldInterpolant) << endl;
  cout << "Interpolant: " << TPTP::toString(interpolant) << endl;
  cout << "Count minimized interpolant: " << TPTP::toString(cntInterpolant) << endl;
  cout << "Quantifiers minimized interpolant: " << TPTP::toString(quantInterpolant) << endl;
}

int ZIE::perform(int argc, char** argv)
{
  CALL("ZIE::perform");


  Unit* z3Refutation = getZ3Refutation();
//  InferenceStore::instance()->outputProof(cout, z3Refutation);

  if(!colorProof(_allUnits, _allUnitsColored)) {
    cout << "Cannot color the refutation" << endl;
    return 1;
  }
  LocalityRestoring locRes(_allUnitsColored, _allUnitsLocal);

  if(!locRes.perform()) {
    cout << "Cannot make the colored proof local" << endl;
    return 1;
  }

  Unit* localRef = _allUnitsLocal.top();

//  InferenceStore::instance()->outputProof(cout, coloredRef);

  outputInterpolantStats(localRef);

  return 0;
}

}
