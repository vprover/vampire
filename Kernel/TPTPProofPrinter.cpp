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
 * @file TPTPProofPrinter.cpp
 * TPTP proof formatting and inference output.
 */

#include "InferenceStore.hpp"
#include "TPTPProofPrinter.hpp"

#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "FormulaVarIterator.hpp"
#include "SortHelper.hpp"
#include "TermIterators.hpp"
#include "Unit.hpp"
#include "HOL/HOL.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Set.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/StringUtils.hpp"
#include "Parse/TPTP.hpp"
#include "SAT/SATInference.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include <sstream>

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
