
/*
 * File Z3InterpolantExtractor.cpp.
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
 * @file Z3InterpolantExtractor.cpp
 * Implements class Z3InterpolantExtractor.
 */

#include <fstream>
#include <iostream>

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/InterpolantMinimizer.hpp"
#include "Shell/LispLexer.hpp"
#include "Shell/Options.hpp"
#include "Shell/TPTPPrinter.hpp"


#include "LocalityRestoring.hpp"

#include "Z3InterpolantExtractor.hpp"

namespace VUtils
{

///////////////////////
// proof extraction
//

vstring ZIE::hypothesesToString(List<TermList>* hypotheses)
{
  vstring res;
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
//  ifstream fin("/work/smt/ticket3i_1_e7_1669.ec.smt2.24");
//  LispLexer lex(fin);
 
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

void LISP_ERROR(vstring error, LExpr* expr)
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
    vstring name = nameE->str;
    _letRecords.push(LetRecord(name, value));
  }
  return true;
}

TermList ZIE::getTermAssignment(vstring name)
{
  CALL("ZIE::getTermAssignment");

  if(!_termAssignments.find(name)) {
    USER_ERROR("unassigned variable "+name);
  }
  return _termAssignments.get(name);
}

ZIE::ProofObject ZIE::getProofObjectAssignment(vstring name)
{
  CALL("ZIE::getProofObjectAssignment");

  if(!_proofAssignments.find(name)) {
    USER_ERROR("unassigned variable "+name);
  }
  return _proofAssignments.get(name);
}

unsigned ZIE::getFunctionNumber(vstring fnName, unsigned arity)
{
  CALL("ZIE::getFunctionNumber");
  bool added;
  unsigned res = env.signature->addFunction(fnName, arity, added);
  if(added) {
    BaseType* type = FunctionType::makeTypeUniformRange(arity, Sorts::SRT_INTEGER, Sorts::SRT_INTEGER);
    env.signature->getFunction(res)->setType(type);
  }
  return res;
}

TermList ZIE::negate(TermList term)
{
  CALL("ZIE::negate");

  unsigned notPred = getFunctionNumber("not", 1);

  if(term.isTerm() && term.term()->functor()==notPred) {
    return *term.term()->nthArgument(0);
  }
  Term* negTrm = Term::create(notPred, 1, &term);
  return TermList(negTrm);
}

bool ZIE::tryReadNumber(LExpr* expr, TermList& res)
{
  CALL("ZIE::tryReadNumber");

  int num;

  if(expr->isAtom() && Int::stringToInt(expr->str, num)) {
    unsigned func = env.signature->addIntegerConstant(IntegerConstantType(num));
    res = TermList(Term::create(func, 0, 0));
    return true;
  }

  LExpr* uminusArg;
  if(expr->get1Arg("-", uminusArg) || expr->get1Arg("~", uminusArg)) {
    if(uminusArg->isAtom() && Int::stringToInt(uminusArg->str, num) && Int::safeUnaryMinus(num, num)) {
      unsigned func = env.signature->addIntegerConstant(IntegerConstantType(num));
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
    vstring name = term->str;

    if(isProofVariable(name)) { LISP_ERROR("proof variable inside term", term); }
    if(isTermVariable(name)) {
      return getTermAssignment(name);
    }

    unsigned func = getFunctionNumber(name, 0);
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
  vstring name = nameE->str;

  TermStack argStack;
  argStack.reset();
  while(args.hasNext()) {
    LExpr* argE = args.next();
    TermList arg = readTerm(argE);
    argStack.push(arg);
  }

  unsigned arity = argStack.size();
  unsigned func = getFunctionNumber(name, arity);
  Term* trm = Term::create(func, arity, argStack.begin());
  TermList res(trm);
  onFunctionApplication(res);
  return res;
}

Formula* ZIE::termToFormula(TermList trm)
{
  CALL("ZIE::termToFormula/1");

  bool added;
  unsigned pred = env.signature->addPredicate("e", 1, added);
  if(added) {
    env.signature->getPredicate(pred)->setType(new PredicateType(Sorts::SRT_INTEGER));
  }

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
    vstring name = expr->str;

    if(isTermVariable(name)) { LISP_ERROR("proof variable expected, term variable found", expr); }
    if(isProofVariable(name)) {
      return getProofObjectAssignment(name);
    }
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

      List<TermList>* remainingHyp = List<TermList>::copy(prem.hypotheses);
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
  vstring name = nameE->toString();

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
    inf = new Inference0(Inference::INPUT);
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
    vstring varName = lrec.first;
    LExpr* expr = lrec.second;
    if(isTermVariable(varName)) {
      TermList trm = readTerm(expr);
      if(!_termAssignments.insert(varName, trm)) {
	USER_ERROR("duplicate variable: " + varName);
      }
    }
    else if(isProofVariable(varName)) {
      ProofObject po = readProofObject(expr);
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

  IntegerConstantType argVal;
  numericArgsOnly = theory->tryInterpretConstant(firstArg, argVal);
  if(numericArgsOnly) {
    minArg = maxArg = argVal;
  }
}

void ZIE::UnaryFunctionInfo::onNewArg(TermList firstArg)
{
  CALL("ZIE::UnaryFunctionInfo::onNewArg");

  if(!numericArgsOnly) {
    return;
  }

  IntegerConstantType argVal;
  if(theory->tryInterpretConstant(firstArg, argVal)) {
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

bool ZIE::colorProof(TermColoring& colorer, UnitStack& derivation, UnitStack& coloredDerivationTgt)
{
  CALL("ZIE::colorProof");

  if(!colorer.areUnitsLocal(_inputUnits)) {
    return false;
  }

  colorer.applyToDerivation(derivation, coloredDerivationTgt);

  return true;
}

TermColoring* ZIE::createRangeColorer()
{
  CALL("ZIE::createRangeColorer");

  RangeColoring* res = new RangeColoring();

  bool first = true;

  IntegerConstantType globalMin;
  IntegerConstantType globalMax;

  UnaryInfoMap::Iterator uiit(_unaryFnInfos);
  while(uiit.hasNext()) {
    UnaryFunctionInfo uinfo;
    unsigned func;
    uiit.next(func, uinfo);
    if(!uinfo.numericArgsOnly) {
      continue;
    }

    if(first || globalMin>uinfo.minArg) {
      globalMin = uinfo.minArg;
    }
    if(first || globalMax<uinfo.maxArg) {
      globalMax = uinfo.maxArg;
    }
    first = false;
    res->addFunction(func);
  }
  IntegerConstantType midpoint = (globalMax+globalMin)/2;
  res->setMiddleValue(midpoint);

  return res;
}

void ZIE::collectSMTLIB1FileFunctionNames(const char* fname, DHSet<vstring>& acc)
{
  CALL("ZIE::collectSMTLIB1FileFunctionNames");

  ifstream inpStm(fname);
  LispLexer lex(inpStm);
  LispParser parser(lex);
  LExpr* parsOut = parser.parse();
  LispListReader parsRdr(parsOut);
  LispListReader bRdr(parsRdr.readList());
  parsRdr.acceptEOL();

  bRdr.acceptAtom("benchmark");
  bRdr.acceptAtom();
  while(bRdr.hasNext()) {
    if(bRdr.tryAcceptAtom(":status")) {
      bRdr.acceptAtom();
    }
    else if(bRdr.tryAcceptAtom(":source")) {
      if(!bRdr.tryAcceptCurlyBrackets()) {
	bRdr.acceptAtom();
      }
    }
    else if(bRdr.tryAcceptAtom(":extrafuns")) {
      LispListReader declsListRdr(bRdr.readList());
      while(declsListRdr.hasNext()) {
	LispListReader declRdr(declsListRdr.readList());
	vstring funName = declRdr.readAtom();
	acc.insert(funName);
      }
    }
    else if(bRdr.tryAcceptAtom(":formula")) {
      bRdr.readNext();
    }
    else {
      //this will always give an error as we have bRdr.hasNext() set to true
      bRdr.acceptEOL();
    }
  }
}

TermColoring* ZIE::createFileColorer(unsigned leftCnt, char** leftFNames, unsigned rightCnt, char** rightFNames)
{
  CALL("ZIE::createFileColorer");

  DHSet<vstring> leftNames;
  for(unsigned i=0; i<leftCnt; i++) {
    collectSMTLIB1FileFunctionNames(leftFNames[i], leftNames);
  }
  DHSet<vstring> rightNames;
  for(unsigned i=0; i<rightCnt; i++) {
    collectSMTLIB1FileFunctionNames(rightFNames[i], rightNames);
  }
  DHSet<vstring> allNames;
  allNames.loadFromIterator(DHSet<vstring>::Iterator(leftNames));
  allNames.loadFromIterator(DHSet<vstring>::Iterator(rightNames));

  DHMap<vstring,Color> nameColors;

  DHSet<vstring>::Iterator nameIt(allNames);
  while(nameIt.hasNext()) {
    vstring name = nameIt.next();
    bool inLeft = leftNames.contains(name);
    bool inRight = rightNames.contains(name);
    ASS(inLeft || inRight);
    Color clr = inLeft ? (inRight ? COLOR_TRANSPARENT : COLOR_LEFT) : COLOR_RIGHT;
    nameColors.insert(name, clr);
  }

  NameMapColoring* res = new NameMapColoring();
  res->loadColors(nameColors);
  return res;
}

/**
 * argc,argv ... arguments related to the choice of term coloring
 */
TermColoring* ZIE::createColorer(unsigned argc, char** argv)
{
  CALL("ZIE::createColorer");

  if(argc==0) {
    return createRangeColorer();
  }
  else {
    unsigned leftColored;
    if(argc<3 || !Int::stringToUnsignedInt(argv[0], leftColored) || leftColored>argc-2) {
      USER_ERROR("expected usage: <number of left colored files> <left colored files> <right colored files>");
    }
    return createFileColorer(leftColored, argv+1, argc-leftColored-1, argv+(1+leftColored));
  }

}

///////////////////////
// main
//

Unit* ZIE::getZ3Refutation()
{
  CALL("ZIE::getZ3Refutation");

  env.colorUsed = true;

  //get the Z3 proof in the form of lisp expressions
    

  LExpr* inp = getInput();

    
  LExpr* proofExpr;
  //get the only child of the lisp expression
  if(!inp->getSingleton(proofExpr)) { LISP_ERROR("invalid proof", inp); }



  //read let expressions into internal structure

  //this one fills _letRecords, in proofExpr will remain the proof expression
  //without the lets that were around it
  while(readLet(proofExpr, proofExpr)) {}

  //this one fills _termAssignments and _proofAssignments based on _letRecords
  processLets();


  //this converts the proof into Vampire's structure
  //ProofObject is an Unit* object together with list of assumptions on which
  //it depends.
  ProofObject pobj = readProofObject(proofExpr);
  //The root proof node should not depend on any assumptions.
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

  if(_showInterpolants) {
    cout << "Old interpolant: " << TPTPPrinter::toString(oldInterpolant) << endl;
    cout << "Interpolant: " << TPTPPrinter::toString(interpolant) << endl;
    cout << "Count minimized interpolant: " << TPTPPrinter::toString(cntInterpolant) << endl;
    cout << "Quantifiers minimized interpolant: " << TPTPPrinter::toString(quantInterpolant) << endl;
  }
}

int ZIE::perform(int argc, char** argv)
{
  CALL("ZIE::perform");

  bool quantifyRed = true;
  if(argc>=3 && argv[2]==vstring("-b")) {
    quantifyRed = false;
    //shift by one argument
    argc--;
    argv++;
  }
  if(argc>=4 && argv[2]==vstring("-t")) {
    unsigned timeLimit;
    ALWAYS(Int::stringToUnsignedInt(argv[3], timeLimit));
    env.options->setTimeLimitInSeconds(timeLimit);
    //shift by two arguments
    argc-=2;
    argv+=2;
  }
  _showInterpolants = true;
  if(argc>=3 && argv[2]==vstring("-q")) {
    _showInterpolants = false;
    //shift by one argument
    argc--;
    argv++;
  }


  getZ3Refutation();
  
    
    
  ScopedPtr<TermColoring> colorer(createColorer(argc-2, argv+2));

  if(!colorProof(*colorer, _allUnits, _allUnitsColored)) {
    cout << "Cannot color the refutation" << endl;
    return 1;
  }
  LocalityRestoring locRes(quantifyRed, _allUnitsColored, _allUnitsLocal);

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
