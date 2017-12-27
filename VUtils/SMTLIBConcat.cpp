
/*
 * File SMTLIBConcat.cpp.
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
 * @file SMTLIBConcat.cpp
 * Implements class SMTLIBConcat.
 */

#include <fstream>

#include "Lib/DHSet.hpp"
#include "Lib/Int.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"

#include "Shell/LispLexer.hpp"

#include "SMTLIBConcat.hpp"

namespace VUtils
{

int SMTLIBConcat::perform(int argc, char** argv)
{
  CALL("SMTLIBConcat::perform");

  Stack<LExpr*> benchExprs;

  for(int i=2; i<argc; i++) {
    LExpr* bench = parseFile(argv[i]);
    benchExprs.push(bench);
  }

  LExpr* merged = mergeBenchmarksIntoSmtlib2(benchExprs);

  rewriteIntsToReals(merged);

//  LExpr* converted = smtlibToSmtlib2(merged);

  cout << merged->toString(false) << endl;

  return 0;
}

LExpr* SMTLIBConcat::extrafuns2decl(LExpr* expr)
{
  CALL("SMTLIBConcat::extrafuns2decl");

  //TODO: currently we handle only constants (on non-constants should fail)
  LispListReader tlRdr(expr);
  LispListWriter res;
  res << "declare-fun"
      << tlRdr.readAtom();
  res << (LispListWriter())
      << tlRdr.readAtom();
  if(tlRdr.hasNext()) {
    USER_ERROR("non-constant functions not supported: "+expr->toString());
  }
  tlRdr.acceptEOL();
  return res.get();
}

void SMTLIBConcat::rewriteSmt1FormToSmt2(LExpr* e0)
{
  CALL("SMTLIBConcat::rewriteSmt1FormToSmt2");

  Stack<LExpr*> toDo;
  toDo.push(e0);

  while(toDo.isNonEmpty()) {
    LExpr* e = toDo.pop();
    if(e->isAtom()) {
      continue;
    }
    else {
      ASS(e->isList());
      LispListReader rdr(e);
      if(rdr.lookAheadAtom("flet") || rdr.lookAheadAtom("let")) {
	LExpr* head = rdr.readNext();
	LExpr* defs = rdr.readNext();
	rdr.readNext();
	rdr.acceptEOL();

	head->str = "let";
	defs->list = (LispListWriter()<<(LispListWriter().append(defs->list))).getList();
      }
      LExprList::Iterator elit(e->list);
      while(elit.hasNext()) {
	toDo.push(elit.next());
      }
    }
  }



}

//LExpr* SMTLIBConcat::smtlibToSmtlib2(LExpr* benchExpr)
//{
//  CALL("SMTLIBConcat::smtlibToSmtlib2");
//  ASS(benchExpr->isList())
//  LispListReader bRdr(benchExpr->list);
//  LispListWriter res;
//
//  bRdr.acceptAtom("benchmark");
//  bRdr.acceptAtom();
//
//  while(bRdr.hasNext()) {
//    if(bRdr.tryAcceptAtom(":status")) {
//      bRdr.acceptAtom();
//    }
//    else if(bRdr.tryAcceptAtom(":source")) {
//      if(!bRdr.tryAcceptCurlyBrackets()) {
//	bRdr.acceptAtom();
//      }
//    }
//    else if(bRdr.tryAcceptAtom(":extrafuns")) {
//      LExprList* funDecls = bRdr.readList();
//      LExprList::Iterator funIt(funDecls);
//      while(funIt.hasNext()) {
//	LExpr* funDecl = funIt.next();
//	res << extrafuns2decl(funDecl);
//      }
//    }
//    else if(bRdr.tryAcceptAtom(":formula")) {
//      LExpr* form = bRdr.readNext();
//      rewriteSmt1FormToSmt2(form);
//      res << (LispListWriter() << "assert" << form);
//    }
//    else {
//      //this will always give an error as we have bRdr.hasNext() set to true
//      bRdr.acceptEOL();
//    }
//  }
//
//  res << (LispListWriter() << "check-sat");
//  res << (LispListWriter() << "get-proof");
//
//  return res.get();
//}

void SMTLIBConcat::rewriteIntsToReals(LExpr* e0)
{
  CALL("SMTLIBConcat::rewriteIntsToReals");

  Stack<LExpr*> toDo;
  toDo.push(e0);

  while(toDo.isNonEmpty()) {
    LExpr* e = toDo.pop();
    if(e->isAtom()) {
      int aux;
      if(Int::stringToInt(e->str, aux)) {
	e->str = e->str+".0";
      }
    }
    else {
      ASS(e->isList());
      LExprList::Iterator leit(e->list);
      while(leit.hasNext()) {
	toDo.push(leit.next());
      }
    }
  }
}

void SMTLIBConcat::addBenchmark(LExpr* expr, DHSet<vstring>& funSet, LispListWriter& wrt)
{
  CALL("SMTLIBConcat::readBenchmark");

  ASS_REP(expr->isList(), expr->toString());

  LispListReader tlRdr(expr->list);
  LExprList* benchLst = tlRdr.readList();
  tlRdr.acceptEOL();

  LispListReader bRdr(benchLst);
  bRdr.acceptAtom("benchmark");
  bRdr.acceptAtom(); //benchmark name
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
      LExprList* funDecls = bRdr.readList();
      LExprList::Iterator funIt(funDecls);
      while(funIt.hasNext()) {
	LExpr* funDecl = funIt.next();
	if(!funDecl->isList() && funDecl->list->head()->isAtom()) { USER_ERROR("function declaration expected: "+funDecl->toString()); }

	vstring fnName = funDecl->list->head()->str;
	if(!funSet.insert(fnName)) {
	  //duplicate function
	  continue;
	}
	wrt << extrafuns2decl(funDecl);
      }
    }
    else if(bRdr.tryAcceptAtom(":formula")) {
      LExpr* form = bRdr.readNext();
      rewriteSmt1FormToSmt2(form);
      wrt << (LispListWriter() << "assert" << form);
    }
    else {
      //this will always give an error as we have bRdr.hasNext() set to true
      bRdr.acceptEOL();
    }
  }
}

LExpr* SMTLIBConcat::mergeBenchmarksIntoSmtlib2(Stack<LExpr*>& exprs)
{
  CALL("SMTLIBConcat::mergeBenchmarks");

  DHSet<vstring> funSet;
  Stack<LExpr*> funs;

  LispListWriter res;
  Stack<LExpr*>::Iterator bit(exprs);
  while(bit.hasNext()) {
    LExpr* benchExpr = bit.next();
    addBenchmark(benchExpr, funSet, res);
  }

//  LispListWriter resBench;
//  resBench << "benchmark" << "unnamed" << ":status" << "unknown";
//
//  Stack<LExpr*>::Iterator funIt(funs);
//  while(funIt.hasNext()) {
//    LExpr* funDecl = funIt.next();
//    resBench << ":extrafuns";
//    resBench << (LispListWriter()<<funDecl);
//  }
//
//  LispListWriter form;
//  form << "and";
//  form.append(formulas);
//
//  resBench << ":formula" << form;

  res << (LispListWriter() << "check-sat");
  res << (LispListWriter() << "get-proof");

  return res.get();
}

LExpr* SMTLIBConcat::parseFile(vstring fname)
{
  CALL("SMTLIBConcat::parseFile");

  if(!System::fileExists(fname)) {
    USER_ERROR("input file does not exist: "+fname);
  }

  ifstream fin(fname.c_str());
  LispLexer lex(fin);
  LispParser parser(lex);
  LExpr* res = parser.parse();

  return res;
}

}
