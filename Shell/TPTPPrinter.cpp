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
 * @file TPTPPrinter.cpp
 * Implements class TPTPPrinter and InferenceStore::TPTPProofPrinter.
 */

#include <sstream>

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Set.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/StringUtils.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "Parse/TPTP.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/InferenceStore.hpp"

#include "Kernel/HOL/HOL.hpp"
#include "SAT/SATInference.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "TPTPPrinter.hpp"

#include "Forwards.hpp"

namespace Shell
{

using namespace std;
TPTPPrinter::TPTPPrinter(std::ostream* tgtStream)
: _tgtStream(tgtStream), _headersPrinted(false)
{
}

/**
 * Print the Unit @param u to the desired output
 */
void TPTPPrinter::print(Unit* u)
{
  std::string body = getBodyStr(u, true);

  ensureHeadersPrinted(u);
  printTffWrapper(u, body);
}

/**
 * Print on the desired output the Unit with the specified name
 * @param name
 * @param u
 */
void TPTPPrinter::printAsClaim(std::string name, Unit* u)
{
  printWithRole(name, "claim", u);
}

void TPTPPrinter::printWithRole(std::string name, std::string role, Unit* u, bool includeSplitLevels)
{
  std::string body = getBodyStr(u, includeSplitLevels);

  ensureHeadersPrinted(u);
  tgt() << "tff(" << name << ", " << role << ", " << body << ")." << endl;
}

/**
 * Return as a std::string the body of the Unit u
 * @param u
 * @param includeSplitLevels
 * @return the body std::string
 */
std::string TPTPPrinter::getBodyStr(Unit* u, bool includeSplitLevels)
{
  std::ostringstream res;

  typedef DHMap<unsigned,TermList, FnvHash, IdentityHash> SortMap;
  static SortMap varSorts;
  varSorts.reset();
  SortHelper::collectVariableSorts(u, varSorts);

  if(u->isClause()) {
    SortMap::Iterator vit(varSorts);
    bool quantified = vit.hasNext();
    if(quantified) {
      res << "![";
      while(vit.hasNext()) {
        unsigned var;
        TermList varSort;
        vit.next(var, varSort);

        res << 'X' << var;
        if(varSort!= AtomicSort::defaultSort()) {
          res << " : " << varSort.toString();
        }
        if(vit.hasNext()) {
          res << ',';
        }
      }
      res << "]: (";
    }

    Clause* cl = static_cast<Clause*>(u);
    auto cit = cl->iterLits();
    if(!cit.hasNext()) {
      res << "$false";
    }
    while(cit.hasNext()) {
      Literal* lit = cit.next();
      res << lit->toString();
      if(cit.hasNext()) {
        res << " | ";
      }
    }

    if(quantified) {
      res << ')';
    }

    if(includeSplitLevels && !cl->noSplits()) {
      auto sit = cl->splits()->iter();
      while(sit.hasNext()) {
        SplitLevel split = sit.next();
        res << " | " << "$splitLevel" << split;
      }
    }
  }
  else {
    return static_cast<FormulaUnit*>(u)->formula()->toString();
  }
  return res.str();
}

/**
 * Surround by tff() the body of the unit u
 * @param u
 * @param bodyStr
 */
void TPTPPrinter::printTffWrapper(Unit* u, std::string bodyStr)
{
  tgt() << "tff(";
  std::string unitName;
  std::filesystem::path unitPath;
  if(Parse::TPTP::findAxiomName(u, unitName, unitPath)) {
    tgt() << unitName;
  }
  else {
    tgt() << "u_" << u->number();
  }
  tgt() << ", ";
  switch(u->inputType()) {
  case UnitInputType::AXIOM:
    tgt() << "axiom"; break;
  case UnitInputType::ASSUMPTION:
    tgt() << "hypothesis"; break;
  case UnitInputType::CONJECTURE:
    tgt() << "conjecture"; break;
  case UnitInputType::NEGATED_CONJECTURE:
    tgt() << "negated_conjecture"; break;
  case UnitInputType::CLAIM:
    tgt() << "claim"; break;
  case UnitInputType::EXTENSIONALITY_AXIOM:
    tgt() << "extensionality"; break;
  default:
     ASSERTION_VIOLATION;
  }
  tgt() << ", " << endl << "    " << bodyStr << " )." << endl;
}

/**
 * Output the symbol definition
 * @param symNumber
 * @param function - true if the symbol is a function symbol
 */
void TPTPPrinter::outputSymbolTypeDefinitions(unsigned symNumber, SymbolType symType)
{
  const Signature::Symbol* sym;
  if(symType == SymbolType::FUNC){
    sym = env.signature->getFunction(symNumber);
  } else if(symType == SymbolType::PRED){
    sym = env.signature->getPredicate(symNumber);
  } else {
    sym = env.signature->getTypeCon(symNumber);
  }
  auto type = sym->type();

  if(type->isAllDefault()) {
    return;
  }

  bool func = symType == SymbolType::FUNC ;
  if(func && theory->isInterpretedConstant(symNumber)) { return; }

  if(sym->interpreted()) {
    Interpretation interp = static_cast<const Signature::InterpretedSymbol*>(sym)->getInterpretation();
    switch(interp) {
    case Theory::INT_SUCCESSOR:
    case Theory::INT_ABS:
    case Theory::INT_DIVIDES:
      //for interpreted symbols that do not belong to TPTP standard we still have to output sort
      break;
    default:
      return;
    }
  }

  std::string cat = "tff(";
  if(env.getMainProblem()->isHigherOrder()){
    cat = "thf(";
  }

  std::string st = "func";
  if(symType == SymbolType::PRED){
    st = "pred";
  } else if(symType == SymbolType::TYPE_CON){
    st = "sort";
  }

  tgt() << cat << st << "_def_" << symNumber << ",type, "
      << sym->name() << ": ";

  tgt() <<  type->toString();

  tgt() << " )." << endl;
}

/**
 * Print only the necessary headers for the sorts. This is needed in order to avoid
 * having in the TPTP problem sorts that are not used
 * @since 08/10/2012, Vienna
 * @author Ioan Dragan
 */
/*void TPTPPrinter::ensureNecesarySorts()
{
  if (_headersPrinted) {
    return;
  }
  unsigned i;
  List<TermList> *_usedSorts(0);
  OperatorType* type;
  const Signature::Symbol* sym;
  unsigned sorts = env.sorts->count();
  //check the sorts of the function symbols and collect information about used sorts
  for (i = 0; i < env.signature->functions(); i++) {
    if(env.signature->isTypeConOrSup(f)){ continue; }
    sym = env.signature->getFunction(i);
    type = sym->type();
    unsigned arity = sym->arity();
    // NOTE: for function types, the last entry (i.e., type->arg(arity)) contains the type of the result
    for (unsigned i = 0; i <= arity; i++) {
      if(! List<unsigned>::member(type->arg(i), _usedSorts))
        List<unsigned>::push(type->arg(i), _usedSorts);
    }
  }
  //check the sorts of the predicates and collect information about used sorts
  for (i = 0; i < env.signature->predicates(); i++) {
    sym = env.signature->getPredicate(i);
    type = sym->type();
    unsigned arity = sym->arity();
    if (arity > 0) {
      for (unsigned i = 0; i < arity; i++) {
        if(! List<unsigned>::member(type->arg(i), _usedSorts))
          List<unsigned>::push(type->arg(i), _usedSorts);
      }
    }
  }
  //output the sort definition for the used sorts, but not for the built-in sorts
  for (i = Sorts::FIRST_USER_SORT; i < sorts; i++) {
    if (List<unsigned>::member(i, _usedSorts))
      tgt() << "tff(sort_def_" << i << ",type, " << env.sorts->sortName(i)
            	      << ": $tType" << " )." << endl;

  }
} */ //TODO fix this function. At the moment, not sure how important it is

/**
 * Makes sure that only the needed headers in the @param u are printed out on the output
 */
void TPTPPrinter::ensureHeadersPrinted(Unit* u)
{
  if(_headersPrinted) {
    return;
  }

  unsigned typeCons = env.signature->typeCons();
  for(unsigned i=Signature::FIRST_USER_CON; i<typeCons; i++) {
    outputSymbolTypeDefinitions(i, SymbolType::TYPE_CON);
  }
  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    outputSymbolTypeDefinitions(i, SymbolType::FUNC);
  }
  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    outputSymbolTypeDefinitions(i, SymbolType::PRED);
  }

  _headersPrinted = true;
}

/**
 * Retrieve the output stream to which vampire prints out
 */
std::ostream& TPTPPrinter::tgt()
{
  if(_tgtStream) {
    return *_tgtStream;
  }
  else {
    return std::cout;
  }
}

/**
 * Return the std::string representing the formula f.
 */
std::string TPTPPrinter::toString(const Formula* formula)
{
  static std::string names [] =
    { "", " & ", " | ", " => ", " <=> ", " <~> ",
      "~", "!", "?", "$term", "$false", "$true", "", ""};
  ASS_EQ(sizeof(names)/sizeof(std::string), NOCONN+1);

  std::string res;

  // render a connective if specified, and then a Formula (or ")" of formula is nullptr)
  typedef pair<Connective,const Formula*> Todo;
  Stack<Todo> stack;

  stack.push(make_pair(NOCONN,formula));

  while (stack.isNonEmpty()) {
    Todo todo = stack.pop();

    // in any case start by rendering the connective passed from "above"
    res += names[todo.first];

    const Formula* f = todo.second;

    if (!f) {
      res += ")";
      continue;
    }

    Connective c = f->connective();

    switch (c) {
    case LITERAL: {
      std::string result = f->literal()->toString();
      if (f->literal()->isEquality()) {
        res += "(" + result + ")";
      } else {
        res += result;
      }
      continue;
    }
    case AND:
    case OR:
      {
        // we will reverse the order
        // but that should not matter

        const FormulaList* fs = f->args();
        res += "(";
        stack.push(make_pair(NOCONN,nullptr)); // render the final closing bracket
        while (FormulaList::isNonEmpty(fs)) {
          const Formula* arg = fs->head();
          fs = fs->tail();
          // the last argument, which will be printed first, is the only one not preceded by a rendering of con
          stack.push(make_pair(FormulaList::isNonEmpty(fs) ? c : NOCONN,arg));
        }

        continue;
      }
    case IMP:
    case IFF:
    case XOR:
      // here we can afford to keep the order right

      res += "(";

      stack.push(make_pair(NOCONN,nullptr)); // render the final closing bracket

      stack.push(make_pair(c,f->right())); // second argument with con

      stack.push(make_pair(NOCONN,f->left())); // first argument without con

      continue;

    case NOT:
      res += "(";

      stack.push(make_pair(NOCONN,nullptr)); // render the final closing bracket

      stack.push(make_pair(c,f->uarg()));

      continue;

    case FORALL:
    case EXISTS:
      {
        std::string result = std::string("(") + names[c] + "[";
        bool needsComma = false;
        VSList::Iterator vs(f->vars());

        while (vs.hasNext()) {
          auto [var, t] = vs.next();

          if (needsComma) {
            result += ", ";
          }
          result += 'X';
          result += Int::toString(var);
          if (t != AtomicSort::defaultSort()) {
            result += " : " + t.toString();
          }
          needsComma = true;
        }
        res += result + "] : (";

        stack.push(make_pair(NOCONN,nullptr));
        stack.push(make_pair(NOCONN,nullptr)); // here we close two brackets

        stack.push(make_pair(NOCONN,f->qarg()));

        continue;
      }

    case BOOL_TERM:
      res += f->getBooleanTerm().toString();

      continue;

    case FALSE:
    case TRUE:
      res += names[c];

      continue;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return res;
}

/**
 * The universal prefix "![X0 : s,X1 : $i] : " binding, with their sorts, all the
 * variables of @param unit; the empty std::string if there are none.
 *
 * Sorts are always spelled out (even the default $i), since making the sorts explicit
 * is the whole point of the prefix. Type variables come first, as they must, and the
 * remaining variables in the order of their numbers, so that the output is stable.
 */
std::string TPTPPrinter::universalPrefix(const Unit* unit)
{
  DHMap<unsigned,TermList, FnvHash, IdentityHash> varSorts;
  SortHelper::collectVariableSorts(const_cast<Unit*>(unit), varSorts);
  if (varSorts.isEmpty()) {
    return "";
  }

  Stack<unsigned> vars;
  vars.loadFromIterator(varSorts.domain());
  vars.sort([&varSorts](unsigned v1, unsigned v2) {
    bool t1 = varSorts.get(v1).isTerm() && varSorts.get(v1).term()->isSuper();
    bool t2 = varSorts.get(v2).isTerm() && varSorts.get(v2).term()->isSuper();
    return (t1 != t2) ? t1 : (v1 < v2);
  });

  std::ostringstream res;
  res << "![";
  for (unsigned i = 0; i < vars.size(); i++) {
    if (i) {
      res << ',';
    }
    res << 'X' << vars[i] << " : " << varSorts.get(vars[i]).toString();
  }
  res << "] : ";
  return res.str();
}

/**
 * Output unit @param unit in TPTP format as a std::string
 *
 * If the unit is a formula of type @b CONJECTURE, output the
 * negation of Vampire's internal representation with the
 * TPTP role conjecture. If it is a clause, just output it as
 * is, with the role negated_conjecture.
 */
std::string TPTPPrinter::toString (const Unit* unit, bool typedClauses)
{
//  const Inference* inf = unit->inference();
//  Inference::Rule rule = inf->rule();

  std::string prefix;
  std::string main = "";

  bool negate_formula = false;
  std::string kind;
  switch (unit->inputType()) {
  case UnitInputType::ASSUMPTION:
    kind = "hypothesis";
    break;

  case UnitInputType::CONJECTURE:
    if(unit->isClause()) {
      kind = "negated_conjecture";
    }
    else {
      negate_formula = true;
      kind = "conjecture";
    }
    break;

  case UnitInputType::EXTENSIONALITY_AXIOM:
    kind = "extensionality";
    break;

  case UnitInputType::NEGATED_CONJECTURE:
    kind = "negated_conjecture";
    break;

  default:
    kind = "axiom";
    break;
  }

  if (unit->isClause()) {
    main = static_cast<const Clause*>(unit)->toTPTPString();
    if (typedClauses) {
      prefix = "tcf";
      main = universalPrefix(unit) + "( " + main + " )";
    } else {
      prefix = "cnf";
    }
  }
  else {
    prefix = "tff";
    const Formula* f = static_cast<const FormulaUnit*>(unit)->formula();
    if(negate_formula) {
      Formula* quant=Formula::quantify(const_cast<Formula*>(f));
      if(quant->connective()==NOT) {
	ASS_EQ(quant, f);
	main = toString(quant->uarg());
      }
      else if(quant->connective()==LITERAL && quant->literal()->isNegative()){
        ASS_EQ(quant,f);
        Literal* comp = Literal::complementaryLiteral(quant->literal());
        main = comp->toString();
      }
      else {
	Formula* neg=new NegatedFormula(quant);
	main = toString(neg);
	neg->destroy();
      }
      if(quant!=f) {
	ASS_EQ(quant->connective(),FORALL);
        VSList::destroy(static_cast<QuantifiedFormula*>(quant)->vars());
	quant->destroy();
      }
    }
    else {
      main = toString(f);
    }
  }

  std::string unitName;
  std::filesystem::path unitPath;
  if(!Parse::TPTP::findAxiomName(unit, unitName, unitPath)) {
    unitName="u" + Int::toString(unit->number());
  }

  return prefix + "(" + unitName + "," + kind + ",\n"
    + "    " + main + ").\n";
}


std::string TPTPPrinter::toString(const Term* t){
  NOT_IMPLEMENTED;
}

std::string TPTPPrinter::toString(const Literal* l){
  NOT_IMPLEMENTED;
}

}

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;
using namespace SAT;

/**
 * Return @b inner quantified over variables in @b vars
 *
 * It is caller's responsibility to ensure that variables in @b vars are unique.
 */
template<typename VarIter>
std::string getQuantifiedStr(VarIter vit, std::string inner, DHMap<unsigned,TermList, FnvHash, IdentityHash>& t_map, bool innerParentheses=true){
  std::string varStr;
  bool first=true;
  while(vit.hasNext()) {
    unsigned var =vit.next();
    std::string ty="";
    TermList t;

    if(t_map.find(var,t)){
      //a variable of a sort other than $i must always be annotated, and
      //preprocessing is not expected to introduce such a sort into an
      //initially untyped problem. Same predicate as Formula::toString.
      ASS(t == AtomicSort::defaultSort() || env.initiallyHasNonDefaultSorts());
      if(env.initiallyHasNonDefaultSorts()){
        ty=" : " + t.toString();
      }
    }
    if(ty == " : $tType"){
      if (!first) { varStr = "," + varStr; }
      varStr=std::string("X")+Int::toString(var)+ty + varStr;
    } else {
      if (!first) { varStr+=","; }
      varStr+=std::string("X")+Int::toString(var)+ty;
    }
    first=false;
  }

  if (first) {
    //we didn't quantify any variable
    return inner;
  }

  if (innerParentheses) {
    return "( ! ["+varStr+"] : ("+inner+") )";
  }
  else {
    return "( ! ["+varStr+"] : "+inner+" )";
  }
}

std::string getQuantifiedStr(VirtualIterator<unsigned> variables, std::string inner,
    DHMap<unsigned, TermList, FnvHash, IdentityHash>& sorts, bool innerParentheses)
{
  return getQuantifiedStr<VirtualIterator<unsigned>>(std::move(variables), inner, sorts, innerParentheses);
}

std::string getQuantifiedStr(Unit* u, List<unsigned>* nonQuantified)
{
  Set<unsigned, FnvHash> vars;
  std::string res;
  DHMap<unsigned,TermList, FnvHash, IdentityHash> t_map;
  SortHelper::collectVariableSorts(u,t_map, /*ignoreBound=*/true);
  if (u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      TermVarIterator vit( (*cl)[i] ); //TODO update iterator for two var lits?
      while(vit.hasNext()) {
        unsigned var=vit.next();
        if (List<unsigned>::member(var, nonQuantified)) {
          continue;
        }
        vars.insert(var);
      }
    }
    res=cl->literalsOnlyToString();
  } else {
    Formula* formula=static_cast<FormulaUnit*>(u)->formula();
    FormulaVarIterator fvit( formula );
    while(fvit.hasNext()) {
      unsigned var=fvit.next();
      if (List<unsigned>::member(var, nonQuantified)) {
        continue;
      }
      vars.insert(var);
    }
    res=formula->toString();
  }

  return getQuantifiedStr(decltype(vars)::Iterator(vars), res, t_map);
}

InferenceStore::TPTPProofPrinter::TPTPProofPrinter(std::ostream& out, InferenceStore* is)
  : AbstractSATProofPrinter(out, is), splitPrefix(Saturation::Splitter::splPrefix)
{}

void InferenceStore::TPTPProofPrinter::print()
{
    //an fof proof needs no type declarations, and the signature can hold a
    //typed symbol no unit ever used, whose declaration would put a tff line
    //into an otherwise fof proof
    if(env.initiallyHasNonDefaultSorts() || env.initiallyHigherOrder()){
      //outputSymbolDeclarations also deals with sorts for now
      //UIHelper::outputSortDeclarations(out);
      UIHelper::outputSymbolDeclarations(out);
    }
    AbstractSATProofPrinter::print();
  }

std::string InferenceStore::TPTPProofPrinter::getRole(InferenceRule rule, UnitInputType origin)
{
    if (isTheoryAxiomRule(rule)) {
      return "axiom";
    }
    switch(rule) {
    case InferenceRule::INPUT:
      if (origin==UnitInputType::CONJECTURE) {
        return "conjecture";
      } else if (origin==UnitInputType::NEGATED_CONJECTURE) {
        return "negated_conjecture";
      } else {
        return "axiom";
      }
    case InferenceRule::NEGATED_CONJECTURE:
      return "negated_conjecture";
    case InferenceRule::AVATAR_DEFINITION:
    case InferenceRule::FUNCTION_DEFINITION:
    case InferenceRule::PREDICATE_DEFINITION:
    case InferenceRule::FOOL_ITE_DEFINITION:
    case InferenceRule::FOOL_LET_DEFINITION:
    case InferenceRule::FOOL_FORMULA_DEFINITION:
    case InferenceRule::FOOL_MATCH_DEFINITION:
    case InferenceRule::GENERAL_SPLITTING_COMPONENT:
    case InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case InferenceRule::EQUALITY_PROXY_DEFINITION:
      return "definition";
    case InferenceRule::THEORY_TAUTOLOGY_SAT_CONFLICT:
    case InferenceRule::HILBERTS_CHOICE_INSTANCE:
    case InferenceRule::DISTINCTNESS_AXIOM:
      return "axiom";
    default:
      return "plain";
    }
  }

std::string InferenceStore::TPTPProofPrinter::tptpRuleName(InferenceRule rule)
{
    return StringUtils::replaceChar(ruleName(rule), ' ', '_');
  }

std::string InferenceStore::TPTPProofPrinter::unitIdToTptp(std::string unitId)
{
    return "f"+unitId;
  }

std::string InferenceStore::TPTPProofPrinter::tptpUnitId(Unit* us)
{
    return unitIdToTptp(Int::toString(us->number()));
  }

std::string InferenceStore::TPTPProofPrinter::tptpDefId(Unit* us)
{
    return unitIdToTptp(Int::toString(us->number())+"_D");
  }

std::string InferenceStore::TPTPProofPrinter::splitsToString(SplitSet* splits)
{
    ASS_G(splits->size(),0);

    if (splits->size()==1) {
      return Saturation::Splitter::getFormulaStringFromName(splits->sval(),true /*negated*/);
    }
    auto sit = splits->iter();
    std::string res("(");
    while(sit.hasNext()) {
      res+= Saturation::Splitter::getFormulaStringFromName(sit.next(),true /*negated*/);
      if (sit.hasNext()) {
	res+=" | ";
      }
    }
    res+=")";
    return res;
  }

std::string InferenceStore::TPTPProofPrinter::getFofString(std::string id, std::string formula, std::string inference, InferenceRule rule, UnitInputType origin)
{
    // use the fragment of the unpreprocessed input: the problem's own
    // hasNonDefaultSorts() and isHigherOrder() are recomputed from the current
    // unit list, so they forget sorts that preprocessing removed, and TPTP
    // conventions allow a proof in a weaker fragment than the input but not in
    // a stronger one
    std::string kind = "fof";
    if(env.initiallyHasNonDefaultSorts()){ kind="tff"; }
    if(env.initiallyHigherOrder()){ kind="thf"; }

    return kind+"("+id+","+getRole(rule,origin)+",("+"\n"
	+"  "+formula+"),\n"
	+"  "+inference+").";
  }

std::string InferenceStore::TPTPProofPrinter::getFormulaString(Unit* us)
{
    std::string formulaStr;
    if (us->isClause()) {
      Clause* cl=us->asClause();
      formulaStr=getQuantifiedStr(cl);
      if (cl->splits() && !cl->splits()->isEmpty()) {
	formulaStr+=" | "+splitsToString(cl->splits());
      }
    }
    else {
      FormulaUnit* fu=static_cast<FormulaUnit*>(us);
      formulaStr=getQuantifiedStr(fu);
    }
    return formulaStr;
  }

bool InferenceStore::TPTPProofPrinter::hasNewSymbols(Unit* u)
{
    bool res = _is->_introducedSymbols.find(u->number());
    ASS(!res || _is->_introducedSymbols.get(u->number()).isNonEmpty());
    if(!res){
      res = _is->_introducedSplitNames.find(u->number());
    }
    return res;
  }

std::string InferenceStore::TPTPProofPrinter::getNewSymbols(std::string origin, std::string symStr)
{
    return "new_symbols(" + origin + ",[" +symStr + "])";
  }

std::string InferenceStore::TPTPProofPrinter::getNewSymbols(std::string origin, SymbolStack::ConstIterator symIt)
{
    std::ostringstream symsStr;
    while(symIt.hasNext()) {
      auto sym = symIt.next();
      symsStr << sym->name();
      if (symIt.hasNext()) { symsStr << ','; }
    }
    return getNewSymbols(origin, symsStr.str());
  }

std::string InferenceStore::TPTPProofPrinter::getNewSymbols(std::string origin, Unit* u)
{
    ASS(hasNewSymbols(u));

    if(_is->_introducedSplitNames.find(u->number())){
      return getNewSymbols(origin,_is->_introducedSplitNames.get(u->number()));
    }

    SymbolStack& syms = _is->_introducedSymbols.get(u->number());
    return getNewSymbols(origin, SymbolStack::ConstIterator(syms));
  }

std::string InferenceStore::TPTPProofPrinter::getSkolemizeMap(Unit* u)
{
  ASS(hasNewSymbols(u));
  SymbolStack& syms = _is->_introducedSymbols.get(u->number());
  return getSkolemizeMap(SymbolStack::ConstIterator(syms));
}

std::string InferenceStore::TPTPProofPrinter::getSkolemizeMap(SymbolStack::ConstIterator symIt)
{
  std::ostringstream symsStr;
  bool hasNext = symIt.hasNext();
  while (hasNext) {
    symsStr << "skolemize(";
    auto symbol = symIt.next();
    auto skolemTerm = _is->_introducedSkolemSymTerms.find(symbol);
    NEVER(skolemTerm.isNone());
    auto skolemizedVariable = _is->_introducedSymbolReplacedVars.find(symbol);
    NEVER(skolemizedVariable.isNone());

    // for now we have to output standard prolog, i.e. f(X1,...,Xn) even in THF
    // TODO: change this once GDV is updated
    std::string skolemStr;
    if (env.higherOrder()) {
      // we require non-lambda terms
      ASS(!TermList(*skolemTerm).isLambdaTerm());
      auto [head, args] = HOL::getHeadAndArgs(TermList(*skolemTerm));
      ASS(head.isTerm() && !head.isLambdaTerm());

      auto h = head.term();
      if(h->isLiteral()) {
        skolemStr = static_cast<Literal*>(h)->predicateName();
      } else if (h->isSort()) {
        skolemStr = static_cast<AtomicSort*>(h)->typeConName();
      } else {
        skolemStr = h->functionName();
      }

      if (h->arity() || args.size()) {
        skolemStr += "(";
        bool first = true;
        for (unsigned i = 0; i < h->arity(); i++) {
          auto v = *h->nthArgument(i);
          ASS(v.isVar());
          if (!first) {
            skolemStr += ",";
          }
          skolemStr += v.toString();
          first = false;
        }
        for (unsigned i = 0; i < args.size(); i++) {
          ASS(args[i].isVar());
          if (!first) {
            skolemStr += ",";
          }
          skolemStr += args[i].toString();
          first = false;
        }
        skolemStr += ")";
      }

    } else {
      skolemStr = (*skolemTerm)->toString();
    }

    symsStr << "X" << *skolemizedVariable << "," << skolemStr << ")";
    hasNext = symIt.hasNext();
    if(hasNext) {
      symsStr << ",";
    }
  }
  return symsStr.str();
}

void InferenceStore::TPTPProofPrinter::printStep(Unit* us)
{
    InferenceRule rule = us->inference().rule();
    UnitIterator parents= us->getParents();

    switch(rule) {
    case InferenceRule::GENERAL_SPLITTING_COMPONENT:
      printGeneralSplittingComponent(us);
      return;
    case InferenceRule::GENERAL_SPLITTING:
      printSplitting(us);
      return;
    default: ;
    }

    //get std::string representing the formula

    std::string formulaStr=getFormulaString(us);

    //get inference std::string

    std::string inferenceStr;
    if (rule==InferenceRule::INPUT) {
      std::string axiomName;
      std::filesystem::path axiomPath;
      if (!Parse::TPTP::findAxiomName(us, axiomName, axiomPath)) {
        // Giles' ucore extraction code parses labels from smtlib files, let's try printing these too
        if (!us->isClause() && us->getFormula()->hasLabel()) {
          axiomName = us->getFormula()->getLabel();
          axiomPath = "unknown";
        } else {
	        axiomName="unknown";
          axiomPath="unknown";
        }
      }
      inferenceStr="file('"+std::string(axiomPath)+"','"+axiomName+"')";
    }
    else if (!parents.hasNext()) {
      std::string newSymbolInfo;
      if (hasNewSymbols(us)) {
        newSymbolInfo = getNewSymbols("definition",us);
        inferenceStr="introduced(definition,["+newSymbolInfo+"],["+tptpRuleName(rule)+"])";
      } else {
        // without introduced symbols we have to claim that the axiom comes from a theory
        inferenceStr="introduced(theory,["+tptpRuleName(rule)+"],[])";
      }
    }
    else {
      ASS(parents.hasNext());
      std::string statusStr;
      if (rule==InferenceRule::SKOLEMIZE) {
	      statusStr="status(esa),"+getNewSymbols("skolem",us) + "," + getSkolemizeMap(us);
      }
      else if(rule==InferenceRule::NEGATED_CONJECTURE) {
	      statusStr="status(cth)";
      }

      inferenceStr="inference("+tptpRuleName(rule);

      inferenceStr+=",["+statusStr+"],[";
      if(rule==InferenceRule::AVATAR_REFUTATION) {
        SATClause *premise = us->inference().satPremise();
        ASS(premise)
        inferenceStr += "s" + Int::toString(premise->number);
      }
      else {
        bool first=true;
        while(parents.hasNext()) {
          Unit* prem=parents.next();
          if (!first) {
            inferenceStr+=',';
          }
          inferenceStr+=tptpUnitId(prem);
          first=false;
        }
      }
      inferenceStr+="])";
    }

    out<<getFofString(tptpUnitId(us), formulaStr, inferenceStr, rule, us->inputType())<<endl;
  }

void InferenceStore::TPTPProofPrinter::printSATStep(SATClause *cl)
{
    out << "cnf(s" << cl->number << ", plain, ";
    if(cl->isEmpty())
      out << "$false";
    else {
      bool first = true;
      for(SATLiteral l : iterTraits(cl->iter())) {
        if(!first)
          out << " | ";
        first = false;
        out << Saturation::Splitter::getFormulaStringFromLiteral(l);
      }
    }

    out << ", inference(";
    auto inference = cl->inference();
    switch(inference->getType()) {
    case SAT::SATInference::PROP_INF: {
      out << "rat,[],[";
      bool first = true;
      SATClauseList *parents =
        static_cast<PropInference *>(inference)->getPremises();
      for(SATClause *parent : iterTraits(parents->iter())) {
        if(!first)
          out << ",";
        first = false;
        out << 's' << parent->number;
      }
      break;
    }
    case SAT::SATInference::FO_CONVERSION:
      out
        << "sat_conversion,[],[f"
        << static_cast<FOConversionInference *>(inference)->getOrigin()->number();
      break;
    }
    out << "])).\n";
  }

void InferenceStore::TPTPProofPrinter::printSplitting(Unit* us)
{
    ASS(us->isClause());

    InferenceRule rule = us->inference().rule();
    UnitIterator parents= us->getParents();
    ASS(rule==InferenceRule::GENERAL_SPLITTING);

    std::string inferenceStr="inference("+tptpRuleName(rule)+",[],[";

    //here we rely on the fact that the base premise is always put as the first premise in
    //GeneralSplitting::apply

    ALWAYS(parents.hasNext());
    Unit* base=parents.next();
    inferenceStr+=tptpUnitId(base);

    ASS(parents.hasNext()); //we always split off at least one component
    while(parents.hasNext()) {
      Unit* comp=parents.next();
      ASS(_is->_splittingNameLiterals.find(comp->number()));
      inferenceStr+=","+tptpDefId(comp);
    }
    inferenceStr+="])";

    out<<getFofString(tptpUnitId(us), getFormulaString(us), inferenceStr, rule)<<endl;
  }

void InferenceStore::TPTPProofPrinter::printGeneralSplittingComponent(Unit* us)
{
    ASS(us->isClause());

    InferenceRule rule = us->inference().rule();
    UnitIterator parents= us->getParents();
    ASS(!parents.hasNext());

    Literal* nameLit=_is->_splittingNameLiterals.get(us->number()); //the name literal must always be stored

    //sorts of the clause's variables, so the quantifiers of the definition
    //below are annotated like every other formula in the proof
    DHMap<unsigned,TermList, FnvHash, IdentityHash> t_map;
    SortHelper::collectVariableSorts(us, t_map);

    std::string defId=tptpDefId(us);

    out<<getFofString(tptpUnitId(us), getFormulaString(us),
	    "inference("+tptpRuleName(InferenceRule::CLAUSIFY)+",[],["+defId+"])", InferenceRule::CLAUSIFY)<<endl;


    List<unsigned>* nameVars=0;
    VariableIterator vit(nameLit);
    while(vit.hasNext()) {
      unsigned var=vit.next().var();
      ASS(!List<unsigned>::member(var, nameVars)); //each variable appears only once in the naming literal
      List<unsigned>::push(var,nameVars);
    }

    std::string compStr;
    List<unsigned>* compOnlyVars=0;
    bool first=true;
    bool multiple=false;
    for (Literal* lit : us->asClause()->iterLits()) {
      if (lit==nameLit) {
	      continue;
      }
      if (first) {
	      first=false;
      }
      else {
	      multiple=true;
	      compStr+=" | ";
      }
      compStr+=lit->toString();

      VariableIterator lvit(lit);
      while(lvit.hasNext()) {
        unsigned var=lvit.next().var();
        if (!List<unsigned>::member(var, nameVars) && !List<unsigned>::member(var, compOnlyVars)) {
          List<unsigned>::push(var,compOnlyVars);
        }
      }
    }
    ASS(!first);

    compStr=getQuantifiedStr(pvi(VList::Iterator(compOnlyVars)), compStr, t_map, multiple);
    List<unsigned>::destroy(compOnlyVars);

    std::string defStr=compStr+" <=> "+Literal::complementaryLiteral(nameLit)->toString();
    defStr=getQuantifiedStr(pvi(VList::Iterator(nameVars)), defStr, t_map);
    List<unsigned>::destroy(nameVars);

    auto nameSymbol = env.signature->getPredicate(nameLit->functor());
    std::ostringstream originStm;
    originStm << "introduced(definition,["
	      << getNewSymbols("definition",nameSymbol->name())
	      << "],[" << tptpRuleName(rule) << "])";

    out<<getFofString(defId, defStr, originStm.str(), rule)<<endl;
  }

} // namespace Kernel
