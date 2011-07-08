/**
 * @file Z3InterpolantExtractor.cpp
 * Implements class Z3InterpolantExtractor.
 */

#include <iostream>

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/LispLexer.hpp"


#include "Z3InterpolantExtractor.hpp"

namespace VUtils
{

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

    LOG("let: " << name << " --> " << value->toString());
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

TermList ZIE::readTerm(LExpr* term)
{
  CALL("ZIE::readTerm");

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

  return TermList(trm);
}

Formula* ZIE::termToFormula(TermList trm)
{
  CALL("ZIE::termToFormula");

  static unsigned pred = env.signature->addPredicate("e", 1);

  Literal* resLit = Literal::create(pred, 1, true, false, &trm);
  return new AtomicFormula(resLit);
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

  LExpr* unaryArg;
  if(expr->get1Arg("hypothesis", unaryArg)) {
    TermList hyp = readTerm(unaryArg);
    List<TermList>* hypLst = 0;
    List<TermList>::push(hyp, hypLst);
    return ProofObject(0, hypLst);
  }

  LExpr* lemmaPrem;
  LExpr* lemmaHypNeg;
  if(expr->get2Args("lemma", lemmaPrem, lemmaHypNeg)) {
    ProofObject prem = readProofObject(lemmaPrem);
    TermList lemmaTrm = readTerm(lemmaHypNeg);
    TermList hyp = negate(lemmaTrm);

    if(!prem.hypotheses->member(hyp)) {
      LISP_ERROR("lemma with non-existing hypothesis", expr);
    }
    if(!prem.unit) {
      LISP_ERROR("invalid lemma premise", expr);
    }

    List<TermList>* remainingHyp = prem.hypotheses->copy();
    remainingHyp = remainingHyp->remove(hyp);

    Inference* inf = new Inference1(Inference::EXTERNAL, prem.unit);
    Formula* lemma = termToFormula(lemmaTrm);
    FormulaUnit* lemmaUnit = new FormulaUnit(lemma, inf, Unit::AXIOM);

    return ProofObject(lemmaUnit, remainingHyp);
  }

  LExprList::Iterator args(expr->list);
  if(!args.hasNext()) { LISP_ERROR("invalid proof object", expr); }
  LExpr* nameE = args.next();
  if(!nameE->isAtom()) { LISP_ERROR("invalid inference rule name", nameE); }
  string name = nameE->str;

  Stack<LExpr*> argStack;
  argStack.reset();
  while(args.hasNext()) {
    LExpr* arg = args.next();
    argStack.push(arg);
  }

  LExpr* conclusionExp = argStack.pop();
  TermList conclusionTrm = readTerm(conclusionExp);
  Formula* conclusion = termToFormula(conclusionTrm);


  DHSet<TermList> hypotheseSet;
  hypotheseSet.reset();
  List<TermList>* hypotheseTerms = 0;
  FormulaList* hypotheses = 0;
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
      Formula* hypothese = termToFormula(hypTrm);
      FormulaList::push(hypothese, hypotheses);
    }
  }

  if(hypotheses) {
    Formula* hypotheseForm;
    if(hypotheses->tail()) {
      hypotheseForm = new JunctionFormula(AND, hypotheses);
    }
    else {
      hypotheseForm = FormulaList::pop(hypotheses);
      ASS(!hypotheses);
    }
    conclusion = new BinaryFormula(IMP, hypotheseForm, conclusion);
  }

  Inference* inf;
  if(name=="asserted") {
    if(premises) { LISP_ERROR("asserted cannot have any premises", expr); }
    inf = new Inference(Inference::INPUT);
  }
  else {
    inf = new InferenceMany(Inference::EXTERNAL, premises);
  }
  FormulaUnit* resUnit = new FormulaUnit(conclusion, inf, Unit::AXIOM);
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
      LOG(varName << " = " << trm.toString());
      if(!_termAssignments.insert(varName, trm)) {
	USER_ERROR("duplicate variable: " + varName);
      }
    }
    else if(isProofVariable(varName)) {
      ProofObject po = readProofObject(expr);
      LOG(varName << " = " << (po.unit ? po.unit->toString() : "<hypothesis>"));
      if(!_proofAssignments.insert(varName, po)) {
	USER_ERROR("duplicate variable: " + varName);
      }
    }
    else {
      USER_ERROR("variable expected: "+varName);
    }

  }
}

int ZIE::perform(int argc, char** argv)
{
  CALL("ZIE::perform");

  LExpr* inp = getInput();
  print(inp);

  LExpr* proofExpr;
  if(!inp->getSingleton(proofExpr)) { LISP_ERROR("invalid proof", inp); }

  while(readLet(proofExpr, proofExpr)) {}

  processLets();

  ProofObject pobj = readProofObject(proofExpr);
  if(pobj.hypotheses) {
    List<TermList>::Iterator hit(pobj.hypotheses);
    string hypStr;
    while(hit.hasNext()) {
      TermList hyp = hit.next();
      hypStr += hyp.toString();
      if(hit.hasNext()) {
	hypStr += ", ";
      }
    }
    USER_ERROR("unresolved hypotheses: " + hypStr);
  }

  InferenceStore::instance()->outputProof(cout, pobj.unit);

  return 0;
}

}
