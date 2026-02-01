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

#include "TermShifter.hpp"
#include "ToPlaceholders.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaVarIterator.hpp"

using IndexVarStack = Stack<std::pair<unsigned, unsigned>>;
using Kernel::Term;

static std::string toStringAux(const Term& term, bool topLevel, IndexVarStack& st);

static std::string termToStr(TermList t, bool topLevel, IndexVarStack& st){
  if (t.isVar())
    return Term::variableToString(t);

  return toStringAux(*t.term(), topLevel, st);
}

static bool findVar(unsigned index, const IndexVarStack & st, unsigned& var) {
  for (const auto & i : st) {
    if (i.first == index) {
      var = i.second;
      return true;
    }
  }
  return false;
}

static std::string lambdaToString(const Term::SpecialTermData* sd, bool pretty)
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
    varList += Term::variableToString(vs.next()) + " : ";
    varList += ss.next().toString();
  }
  varList += pretty ? "" : "]";
  std::string lambda = pretty ? "λ" : "^";

  return "(" + lambda + varList + " : (" + lambdaExp.toString() + "))";
}

static std::string toStringAux(const Term& term, bool topLevel, IndexVarStack& st) {

  using Shell::Options;
  using namespace Kernel;

  ASS(!term.isLiteral())

  auto printSetting = env.options->holPrinting();
  bool pretty = printSetting == Options::HPrinting::PRETTY;
  bool printDB = printSetting == Options::HPrinting::DB_INDICES;

  std::string res;

  if (term.isSpecial()) {
    const auto sd = term.getSpecialData();

    if (term.isFormula())
      return sd->getFormula()->toString();
    if (term.isLambda())
      return lambdaToString(sd, pretty);

    // currently HOL doesn't support any other specials
    ASSERTION_VIOLATION
  }

  if (term.isArrowSort()) {
    ASS(term.arity() == 2)
    auto arg1 = term.nthArgument(0);
    auto arg2 = term.nthArgument(1);
    std::string arrow = pretty ? " → " : " > ";
    res += topLevel ? "" : "(";
    res += termToStr(*arg1, false, st) + arrow + termToStr(*arg2, true, st);
    res += topLevel ? "" : ")";
    return res;
  }

  if (term.isSort()) {
    auto sort = static_cast<const AtomicSort*>(&term);
    if (sort->isBoolSort() && pretty)
      return "ο";
    if (sort->functor() == Signature::DEFAULT_SORT_CON && pretty)
      return "ι";

    // any non-arrow sort
    res = sort->typeConName();
    if (pretty && term.arity())
      res += "⟨";
    for (unsigned i = 0; i < term.arity(); i++) {
      if (pretty && i != 0)
        res += ", ";

      if (!pretty)
        res += " @ ";

      res += termToStr(*term.nthArgument(i), pretty, st);
    }

    if (pretty && term.arity() > 0)
      res += "⟩";
    return res;
  }

  if (term.isPlaceholder()) {
    return term.functionName() + "⟨" + term.nthArgument(0)->toString(true) + "⟩";
  }

  if (term.isLambdaTerm()) {
    unsigned v = st.size() ? st.top().second + 1 : 0;
    std::string bvar = (pretty ? "y" : "Y") + Int::toString(v);
    bvar = pretty ?
                  bvar + " : " + termToStr(*term.nthArgument(0), true, st) :
                  "[" + bvar + " : " + termToStr(*term.nthArgument(0), true, st) + "]";
    bvar = printDB ? "db" + Int::toString(v) + " : " + termToStr(*term.nthArgument(0), true, st) : bvar;

    IndexVarStack newSt(st);
    for (auto &[fst, snd] : newSt)
      ++fst;

    newSt.push(std::make_pair(0, v));

    std::string sep = pretty || printDB ? ". " : ": ";
    std::string lambda = pretty ? "λ" : "^";
    std::string lbrac = pretty ? "" : "(";
    std::string rbrac = pretty ? "" : ")";

    res = "(" + lambda + bvar + sep +  lbrac + termToStr(*term.nthArgument(2), !pretty, newSt) + rbrac + ")";
    return res;
  }

  auto dbOption = term.deBruijnIndex();
  if (dbOption.isSome() && !printDB) {
    auto db = dbOption.unwrap();
    if (unsigned var; findVar(db, st, var))
      return (pretty ? "y" : "Y") + Int::toString(var);

    // loose bound index
    return "db" + Int::toString(db);
  }

  auto [head, args] = HOL::getHeadAndArgs(TermList(&term));
  bool hasArgs = args.size();

  std::string headStr;
  if (head.isVar() || (head.deBruijnIndex().isSome() && !printDB) || head.isLambdaTerm() || head.term()->isSpecial())
    headStr = termToStr(head, false, st);
  else if (head.isChoice())
    headStr = pretty ? "ε" : "@@+";
  else if (HOL::isTrue(head))
    headStr = pretty ? "⊤" : "$true";
  else if (HOL::isFalse(head))
    headStr = pretty ? "⊥" : "$false";
  else {
    using ProxyEntry = std::tuple<Proxy, std::string, std::string>;

    auto functorProxy = env.signature->getFunction(head.term()->functor())->proxy();

    static const std::initializer_list<ProxyEntry> proxySymbols = {
      {Proxy::NOT,      "¬",  "~"   },
      {Proxy::SIGMA,    "Σ",  "??"  },
      {Proxy::PI,       "Π",  "!!"  },
      {Proxy::AND,      "∧",  "&"   },
      {Proxy::OR,       "∨",  "|"   },
      {Proxy::XOR,      "⊕", "<~>" },
      {Proxy::IMP,      "⇒", "=>"  },
      {Proxy::IFF,      "≈",  "="   },
      {Proxy::EQUALS,   "≈",  "="   }
    };

    bool foundProxy = false;
    for (const auto& [proxy, ifPretty, otherwise] : proxySymbols) {
      if (proxy == functorProxy) {
        headStr = pretty ? ifPretty : otherwise;
        foundProxy = true;
        break;
      }
    }

    if (!foundProxy) {
      headStr = head.term()->functionName();
      if (head.deBruijnIndex().isSome())
        headStr = headStr + "_" + Int::toString(head.deBruijnIndex().unwrap());
    }
  }

  if (head.isTerm() && !head.isProxy(Proxy::EQUALS) && head.deBruijnIndex().isNone() &&
      !head.isLambdaTerm() && head.term()->arity() > 0) {
    auto t = head.term();
    if (pretty)
      headStr += "⟨";
    for (unsigned i = 0; i < t->arity(); ++i) {
      headStr += pretty && i != 0 ? ", " : "";
      headStr += !pretty ? " @ " : "";
      headStr += termToStr(*t->nthArgument(i),pretty,st);
    }
    if (pretty) headStr += "⟩";
  }

  if (!topLevel && hasArgs)
    res += "(";

  static constexpr auto proxies = std::initializer_list<Proxy> {
      Proxy::AND, Proxy::OR, Proxy::IFF, Proxy::EQUALS, Proxy::IMP, Proxy::XOR
  };

  if (std::any_of(proxies.begin(), proxies.end(), [&term = head](Proxy proxy) { return term.isProxy(proxy); }) &&
      args.size() == 2) {
    res += termToStr(args[1], false, st) + " " + headStr + " " + termToStr(args[0], false, st);
  } else {
    std::string app = pretty || head.isProxy(Proxy::NOT) ? " " : " @ ";
    res += headStr;
    while (!args.isEmpty()) {
      res += app + termToStr(args.pop(), false, st);
    }
  }
  res += (!topLevel && hasArgs) ? ")" : "";
  return res;
}

std::string HOL::toString(const Term& term, bool topLevel) {
  IndexVarStack st;

  return toStringAux(term, topLevel, st);
}

TermList HOL::matrix(TermList t) {
  while (t.isLambdaTerm()) {
    t = t.lambdaBody();
  }
  return t;
}

TermList HOL::getHeadAndArgs(TermList term, TermStack& args) {
  args.reset();

  term = matrix(term);

  while (term.isApplication()) {
    args.push(term.rhs());
    term = term.lhs();
  }

  return term;
}

std::pair<TermList, TermStack> HOL::getHeadAndArgs(TermList term) {
  TermStack stack;
  TermList head = getHeadAndArgs(term, stack);

  return {head, stack};
}

/** indexed from 1 */
TermList HOL::getNthArg(TermList arrowSort, unsigned argNum) {
  ASS(argNum > 0)

  TermList res;
  while (argNum >= 1) {
    ASS(arrowSort.isArrowSort())

    res = arrowSort.domain();
    arrowSort = arrowSort.result();
    argNum--;
  }
  return res;
}

/** indexed from 1 */
TermList HOL::getResultAppliedToNArgs(TermList arrowSort, unsigned argNum) {
  while (argNum > 0) {
    ASS(arrowSort.isArrowSort())
    arrowSort = arrowSort.result();
    argNum--;
  }
  return arrowSort;
}

unsigned HOL::getArity(TermList sort) {
  unsigned arity = 0;
  while (sort.isArrowSort()) {
    sort = sort.result();
    arity++;
  }
  return arity;
}

TermList HOL::getDeBruijnIndex(int index, TermList sort) {
  unsigned fun = env.signature->getDeBruijnIndex(index);
  return TermList(Term::create1(fun, sort));
}

void HOL::getArgSorts(TermList t, TermStack* sorts) {
  while (t.isArrowSort()) {
    sorts->push(t.domain());
    t = t.result();
  }

  t = matrix(t);

  while (t.isApplication()) {
    sorts->push(*t.term()->nthArgument(0));
    t = t.lhs();
  }
}

TermStack HOL::getArgSorts(TermList t) {
  TermStack stack;
  getArgSorts(t, &stack);

  return stack;
}

void HOL::getHeadSortAndArgs(TermList term, TermList& head, TermList& headSort, TermStack& args) {
  if (!args.isEmpty())
    args.reset();

  term = matrix(term);
  while (term.isApplication()) {
    args.push(term.rhs());
    TermList t = term.lhs();
    if (!t.isApplication())
      headSort = lhsSort(term);

    term = t;
  }
  head = term;
}

void HOL::getHeadArgsAndArgSorts(TermList t, TermList& head, TermStack& args, TermStack& argSorts) {
  if (!args.isEmpty())
    args.reset();

  if (!argSorts.isEmpty())
    argSorts.reset();

  t = matrix(t);

  while (t.isApplication()) {
    args.push(t.rhs());
    argSorts.push(rhsSort(t));
    t = t.lhs();
  }

  head = t;
}

TermList HOL::lhsSort(TermList t) {
  ASS(t.isApplication())

  return AtomicSort::arrowSort(*t.term()->nthArgument(0),
                               *t.term()->nthArgument(1));
}

TermList HOL::rhsSort(TermList t) {
  ASS(t.isApplication())

  return *t.term()->nthArgument(0);
}

TermList HOL::finalResult(TermList sort)
{
  if (sort.isVar() || !sort.isArrowSort()) {
    return sort;
  }
  while (sort.isArrowSort()) {
    sort = sort.result();
  }
  return sort;
}

void HOL::getMatrixAndPrefSorts(TermList t, TermList& matrix, TermStack& sorts) {
  while (t.isLambdaTerm()) {
    sorts.push(*t.term()->nthArgument(0));
    t = t.lambdaBody();
  }
  matrix = t;
}

std::optional<TermList> HOL::isEtaExpandedVar(TermList body) {
  unsigned l = 0; // number of lambda binders
  while (body.isLambdaTerm()) {
    l++;
    body = body.lambdaBody();
  }

  unsigned n = 0; // number of De bruijn indices at end of term
  while (body.isApplication()) {
    auto dbIndex = body.rhs().deBruijnIndex();
    if (!dbIndex.isSome() || dbIndex.unwrap() != n)
      break;
    body = body.lhs();
    n++;
  }

  return n == l && body.isVar() ? std::optional(body) : std::nullopt;
}

std::pair<TermList, TermList> HOL::normaliseLambdaPrefixes(TermList t1, TermList t2) {
  if (t1.isVar() && t2.isVar())
    return {t1, t2};

  TermList nonVar = t1.isVar() ? t2 : t1;
  TermList sort = SortHelper::getResultSort(nonVar.term());

  auto etaExpand = [](TermList t, TermList sort, TermStack* sorts, unsigned n){
    TermStack sorts1; // sorts of new prefix

    t = TermShifter::shift(t, n).first; // lift loose indices by n

    for(int i = n - 1; i >= 0; i--) { // append De Bruijn indices
      ASS(sort.isArrowSort())

      auto s = sort.domain();
      auto dbIndex = getDeBruijnIndex(i, s);
      t = create::app(sort, t, dbIndex);
      sort = sort.result();
      sorts1.push(s);
    }

    while (!sorts1.isEmpty()) { // wrap in new lambdas
      t = create::namelessLambda(sorts1.pop(), t);
    }

    while (!sorts->isEmpty()) { // wrap in original lambdas
      t = create::namelessLambda(sorts->pop(), t);
    }

    return t;
  };

  unsigned m = 0, n = 0;
  TermList t1_body = t1, t2_body = t2, t1_sort = sort, t2_sort = sort;
  TermStack prefSorts1, prefSorts2;

  while (t1_body.isLambdaTerm()) {
    t1_body = t1_body.lambdaBody();
    prefSorts1.push(t1_sort.domain());
    t1_sort = t1_sort.result();
    m++;
  }

  while (t2_body.isLambdaTerm()) {
    t2_body = t2_body.lambdaBody();
    prefSorts2.push(t2_sort.domain());
    t2_sort = t2_sort.result();
    n++;
  }

  if (m > n)
    return {t1, etaExpand(t2_body, t2_sort, &prefSorts2, m - n)};
  if (n > m)
    return {etaExpand(t1_body, t1_sort, &prefSorts1, n - m), t2};

  return {t1, t2};
}

TermStack HOL::getFlexHeadSorts(TermList flexTerm, TermList rigidTermSort) {
  TermStack sorts;
  TermList matrixSort;
  if (flexTerm.isVar()) {
    matrixSort = rigidTermSort;
  } else {
    matrixSort = flexTerm.resultSort();
    while (flexTerm.isLambdaTerm()) {
      matrixSort = *flexTerm.term()->nthArgument(1);
      flexTerm = flexTerm.lambdaBody();
    }
  }

  TermStack temp;
  getArgSorts(matrixSort, &temp);

  while (!temp.isEmpty())
    sorts.push(temp.pop());

  getArgSorts(flexTerm, &sorts);
  return sorts;
}

bool HOL::getProjAndImitBindings(TermList flexTerm, TermList rigidTerm, TermStack* bindings, TermList* fVar) {

  ASS(bindings->isEmpty())

  // since term is rigid, cannot be a variable
  TermList sort = finalResult(matrix(rigidTerm).resultSort());
  TermList headRigid = rigidTerm.head();


  auto [headFlex, argsFlex] = getHeadAndArgs(flexTerm);

  TermStack sortsFlex = getFlexHeadSorts(flexTerm, rigidTerm.resultSort()); //sorts of arguments of flex head

  TermList pb;
  TermList var = *fVar;
  bool imit = false;

  // imitation
  if (headRigid.deBruijnIndex().isNone()) { // cannot imitate a bound variable
    imit = true;

    // pb = createGeneralBinding(var, headRigid, sortsFlex); TODO
    if (var.var() > fVar->var())
      *fVar = var;

    bindings->push(pb);
  }

  ASS(sortsFlex.size() >= argsFlex.size());
  unsigned diff = sortsFlex.size() - argsFlex.size();

  // projections
  for (unsigned i = 0; i < argsFlex.size(); i++) {
    // try and project each of the arguments of the flex head in turn
    TermList arg = argsFlex[i];
    TermList argSort = sortsFlex[i + diff];

    // sort wrong, cannot project this arg
    if(finalResult(argSort) != sort)
      continue;

    TermList head = arg.head();

    // argument has a rigid head different to that of rhs. no point projecting
    if(head.isTerm() &&  head.deBruijnIndex().isNone() &&  head != headRigid)
      continue;

    TermList dbi = getDeBruijnIndex(i + diff, sortsFlex[i + diff]);

    TermList pb = createGeneralBinding(fVar, dbi, &sortsFlex);
    if (var.var() > fVar->var())
      *fVar = var;
    bindings->push(pb);
  }

  return imit;
}

TermList HOL::createGeneralBinding(TermList* freshVar, TermList head, TermStack* sorts, bool surround) {
  ASS(head.isTerm()) // in the future may wish to reconsider this assertion

  TermStack args;
  TermStack argSorts = getArgSorts(head.resultSort());
  TermStack indices;

  auto getNextFreshVar = [&]() -> TermList {
    // TODO MH
    // freshVar = TermList(freshVar.var() + 1, freshVar.bank());
    return *freshVar;
  };

  for (unsigned i = 0; i < sorts->size(); i++) {
    indices.push(getDeBruijnIndex(i, (*sorts)[i]));
  }

  while (!argSorts.isEmpty()) {
    TermList varSort = AtomicSort::arrowSort(*sorts, argSorts.pop());
    args.push(create::app(varSort, getNextFreshVar(), indices));
  }

  TermList pb = create::app(head, args);
  return surround ? create::surroundWithLambdas(pb, *sorts) : pb;
}