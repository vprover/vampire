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
 * @file HOL.cpp
 */

#include "Kernel/HOL/HOL.hpp"

#include "Kernel/Formula.hpp"

using IndexVarStack = Stack<std::pair<int, unsigned>>;


std::string toStringAux(const Kernel::Term* term, bool topLevel, IndexVarStack& st);

static std::string termToStr(TermList t, bool topLevel, IndexVarStack& st){
  if (t.isVar()) {
    return Kernel::Term::variableToString(t);
  }
  return toStringAux(t.term(), topLevel, st);
}

static void incrementAll(IndexVarStack& st) {
  for (auto & i : st) {
    ++i.first;
  }
}

static bool findVar(int index, IndexVarStack& st, unsigned& var) {
  for (const auto & i : st) {
    if (i.first == index) {
      var = i.second;
      return true;
    }
  }
  return false;
}

static std::string lambdaToString(const Kernel::Term::SpecialTermData* sd, bool pretty)
{
  Kernel::VList *vars = sd->getLambdaVars();
  Kernel::SList * sorts = sd->getLambdaVarSorts();
  TermList lambdaExp = sd->getLambdaExp();

  std::string varList = pretty ? "" : "[";

  Kernel::VList::Iterator vs(vars);
  Kernel::SList::Iterator ss(sorts);

  bool first = true;
  while (vs.hasNext()) {
    varList += first ? "" : ", ";
    first = false;
    varList += Kernel::Term::variableToString(vs.next()) + " : ";
    varList += ss.next().toString();
  }
  varList += pretty ? "" : "]";
  std::string lambda = pretty ? "λ" : "^";

  return "(" + lambda + varList + " : (" + lambdaExp.toString() + "))";
}

std::string toStringAux(const Kernel::Term* term, bool topLevel, IndexVarStack& st) {

  using Kernel::Term;
  using Shell::Options;


  ASS(!term->isLiteral())

  auto printSetting = env.options->holPrinting();
  bool pretty = printSetting == Options::HPrinting::PRETTY;
  bool printDB = printSetting == Options::HPrinting::DB_INDICES;

  std::string res;

  if (term->isSpecial()) {
    const auto sd = term->getSpecialData();

    if (term->isFormula())
      return sd->getFormula()->toString();
    if (term->isLambda())
      return lambdaToString(sd, pretty);

    // currently HOL doesn't support any other specials
    ASSERTION_VIOLATION
  }

  if (term->isArrowSort()) {
    ASS(term->arity() == 2);
    auto arg1 = term->nthArgument(0);
    auto arg2 = term->nthArgument(1);
    std::string arrow = pretty ? " → " : " > ";
    res += topLevel ? "" : "(";
    res += termToStr(*arg1, false, st) + arrow + termToStr(*arg2, true, st);
    res += topLevel ? "" : ")";
    return res;
  }

  if (term->isSort()) {
    auto sort = static_cast<const Kernel::AtomicSort *>(term);
    if (sort->isBoolSort() && pretty)
      return "ο";
    if (sort->functor() == Kernel::Signature::DEFAULT_SORT_CON && pretty)
      return "ι";

    // any non-arrow sort
    res = sort->typeConName();
    if (pretty && term->arity())
      res += "⟨";
    for (unsigned i = 0; i < term->arity(); i++) {
      if (pretty && i != 0)
        res += ", ";

      if (!pretty)
        res += " @ ";

      res += termToStr(*term->nthArgument(i), pretty, st);
    }

    if (pretty && term->arity() > 0)
      res += "⟩";
    return res;
  }

  if (term->isLambdaTerm()) {
    unsigned v = st.size() ? st.top().second + 1 : 0;
    std::string bvar = (pretty ? "y" : "Y") + Int::toString(v);
    bvar = pretty ?
                  bvar + " : " + termToStr(*term->nthArgument(0),true,st) :
                  "[" + bvar + " : " + termToStr(*term->nthArgument(0),true,st) + "]";
    bvar = printDB ? "db" + Int::toString(v) + " : " + termToStr(*term->nthArgument(0),true,st) : bvar;

    IndexVarStack newSt(st);
    incrementAll(newSt);
    newSt.push(std::make_pair(0, v));

    std::string sep = pretty || printDB ? ". " : ": ";
    std::string lambda = pretty ? "λ" : "^";
    std::string lbrac = pretty ? "" : "(";
    std::string rbrac = pretty ? "" : ")";

    res = "(" + lambda + bvar + sep +  lbrac + termToStr(*term->nthArgument(2), !pretty, newSt) + rbrac + ")";
    return res;
  }

  auto dbOption = term->deBruijnIndex();
  if (dbOption.isSome() && !printDB) {
    auto db = dbOption.unwrap();
    unsigned var;
    if (findVar(db, st, var))
      return (pretty ? "y" : "Y") + Int::toString(var);

    // loose bound index
    return "db" + Int::toString(db);
  }

  // TODO: MH
  TermList head;
  Kernel::TermStack args;
  HOL::getHeadAndArgs(this, head, args);
  bool hasArgs = args.size();

  std::string headStr;
  if(head.isVar() || (head.deBruijnIndex().isSome() && !db) || head.isLambdaTerm() || head.term()->isSpecial()){
    headStr = termToStr(head,false,st);
  }
  // else if(head.isNot()){ headStr = pretty ? "¬" : "~"; }
  // else if(head.isSigma()){ headStr = pretty ? "Σ" : "??"; }
  // else if(head.isPi()){ headStr = pretty ? "Π" : "!!"; }
  // else if(head.isAnd()){ headStr = pretty ? "∧" : "&"; }
  // else if(head.isOr()){ headStr = pretty ? "∨" : "|"; }
  // else if(head.isXOr()){ headStr = pretty ? "⊕" : "<~>"; }
  // else if(head.isImp()){ headStr = pretty ? "⇒" : "=>"; }
  // else if(head.isChoice()){ headStr = pretty ? "ε" : "@@+"; }
  // else if(head.isIff() || head.isEquals()){ headStr = pretty ? "≈" : "="; } // @=???
  // else if(HOL::isTrue(head)){ headStr = pretty ? "⊤" : "$true"; }
  // else if(HOL::isFalse(head)){ headStr = pretty ? "⊥" : "$false"; }
  // else {
  //   headStr = head.term()->functionName();
  //   if(head.deBruijnIndex().isSome()){
  //     headStr = headStr + "_" + Int::toString(head.deBruijnIndex().unwrap());
  //   }
  // }
  //
  // if(head.isTerm() && !head.isEquals() && head.deBruijnIndex().isNone() &&
  //     !head.isLambdaTerm() && head.term()->arity()){
  //   Term* t = head.term();
  //   if(pretty) headStr += "⟨";
  //   for(unsigned i = 0; i < t->arity(); i++){
  //     headStr += pretty && i != 0 ? ", " : "";
  //     headStr += !pretty ? " @ " : "";
  //     headStr += termToStr(*t->nthArgument(i),pretty,st);
  //   }
  //   if(pretty) headStr += "⟩";
  // }
  //
  // res += (!topLevel && hasArgs) ? "(" : "";
  //
  // if((head.isAnd() || head.isOr() || head.isIff() || head.isEquals() || head.isImp() || head.isXOr()) &&
  //     args.size() == 2){
  //   res += termToStr(args[1],false,st) + " " + headStr + " " + termToStr(args[0],false,st);
  // } else {
  //   vstring app = pretty || head.isNot() ? " " : " @ ";
  //   res += headStr;
  //   while(!args.isEmpty()){
  //     res += app + termToStr(args.pop(),false,st);
  //   }
  // }
  // res += (!topLevel && hasArgs) ? ")" : "";
  return res;
}

std::string HOL::toString(const Kernel::Term* term, bool topLevel) {
  IndexVarStack st;

  return toStringAux(term, topLevel, &st);
}
