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
 * @file InferenceStore.cpp
 * Implements class InferenceStore.
 */

#include "Lib/Allocator.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/StringUtils.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Sort.hpp"

#include "Shell/LaTeX.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Parse/TPTP.hpp"

#include "Saturation/Splitter.hpp"

#include "Signature.hpp"
#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "FormulaVarIterator.hpp"
#include "Inference.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"
#include "SortHelper.hpp"
#include "Problem.hpp"

#include "InferenceStore.hpp"

//TODO: when we delete clause, we should also delete all its records from the inference store

namespace Kernel
{

using namespace std;
using namespace Lib;
using namespace Shell;

void InferenceStore::FullInference::increasePremiseRefCounters()
{
  for(unsigned i=0;i<premCnt;i++) {
    if (premises[i]->isClause()) {
      premises[i]->incRefCnt();
    }
  }
}



InferenceStore::InferenceStore()
{
}

vstring InferenceStore::getUnitIdStr(Unit* cs)
{
  if (!cs->isClause()) {
    return Int::toString(cs->number());
  }
  return Int::toString(cs->number());
}

/**
 * Records informations needed for outputting proofs of general splitting
 */
void InferenceStore::recordSplittingNameLiteral(Unit* us, Literal* lit)
{
  //each clause is result of a splitting only once
  ALWAYS(_splittingNameLiterals.insert(us, lit));
}


/**
 * Record the introduction of a new symbol
 */
void InferenceStore::recordIntroducedSymbol(Unit* u, SymbolType st, unsigned number)
{
  SymbolStack* pStack;
  _introducedSymbols.getValuePtr(u->number(),pStack);
  pStack->push(SymbolId(st,number));
}

/**
 * Record the introduction of a split name
 */
void InferenceStore::recordIntroducedSplitName(Unit* u, vstring name)
{
  ALWAYS(_introducedSplitNames.insert(u->number(),name));
}

/**
 * Get the parents of unit represented by us and fill in the rule used to generate this unit
 *
 * This will first check if the unit was generated by a special inference that was
 * recorded in the InferenceStore and if not, use the inference stored in the unit itself
 */
UnitIterator InferenceStore::getParents(Unit* us, InferenceRule& rule)
{
  ASS_NEQ(us,0);

  // The unit itself stores the inference
  UnitList* res = 0;
  Inference& inf = us->inference();

  // opportunity to shrink the premise list
  // (currently applies if this was a SAT-based inference
  // and the solver didn't provide a proper proof nor a core)
  inf.minimizePremises();

  Inference::Iterator iit = inf.iterator();
  while(inf.hasNext(iit)) {
    Unit* premUnit = inf.next(iit);
    UnitList::push(premUnit, res);
  }
  rule = inf.rule();
  res = UnitList::reverse(res); //we want items in the same order
  return pvi(UnitList::DestructiveIterator(res));
}

/**
 * Get parents where we do not care about the generating rule
 */
UnitIterator InferenceStore::getParents(Unit* us)
{
  InferenceRule aux;
  return getParents(us, aux);
}

/**
 * Return @b inner quantified over variables in @b vars
 *
 * It is caller's responsibility to ensure that variables in @b vars are unique.
 */
template<typename VarContainer>
vstring getQuantifiedStr(const VarContainer& vars, vstring inner, DHMap<unsigned,TermList>& t_map, bool innerParentheses=true){
  VirtualIterator<unsigned> vit=pvi( getContentIterator(vars) );
  vstring varStr;
  bool first=true;
  while(vit.hasNext()) {
    unsigned var =vit.next();
    vstring ty="";
    TermList t;

    if(t_map.find(var,t) && env.getMainProblem()->hasNonDefaultSorts()){
      //hasNonDefaultSorts is true if the problem contains a sort
      //that is not $i and not a variable
      ty=" : " + t.toString();
    }
    if(ty == " : $tType"){
      if (!first) { varStr = "," + varStr; }
      varStr=vstring("X")+Int::toString(var)+ty + varStr;
    } else {
      if (!first) { varStr+=","; }
      varStr+=vstring("X")+Int::toString(var)+ty;
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

/**
 * Return @b inner quentified over variables in @b vars
 *
 * It is caller's responsibility to ensure that variables in @b vars are unique.
 */
template<typename VarContainer>
vstring getQuantifiedStr(const VarContainer& vars, vstring inner, bool innerParentheses=true)
{
  static DHMap<unsigned,TermList> d;
  return getQuantifiedStr(vars,inner,d,innerParentheses);
}

/**
 * Return vstring containing quantified unit @b u.
 */
vstring getQuantifiedStr(Unit* u, List<unsigned>* nonQuantified=0)
{
  Set<unsigned> vars;
  vstring res;
  DHMap<unsigned,TermList> t_map;
  SortHelper::collectVariableSorts(u,t_map);
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

  return getQuantifiedStr(vars, res, t_map);
}

struct UnitNumberComparator
{
  static Comparison compare(Unit* u1, Unit* u2)
  {
    return Int::compare(u1->number(), u2->number());
  }
};

struct InferenceStore::ProofPrinter
{
  ProofPrinter(ostream& out, InferenceStore* is)
  : _is(is), out(out)
  {
    outputAxiomNames=env.options->outputAxiomNames();
    delayPrinting=true;
  }

  void scheduleForPrinting(Unit* us)
  {
    outKernel.push(us);
    handledKernel.insert(us);
  }

  virtual ~ProofPrinter() {}

  virtual void print()
  {
    while(outKernel.isNonEmpty()) {
      Unit* cs=outKernel.pop();
      handleStep(cs);
    }
    if(delayPrinting) printDelayed();
  }

protected:

  virtual bool hideProofStep(InferenceRule rule)
  {
    return false;
  }

  void requestProofStep(Unit* prem)
  {
    if (!handledKernel.contains(prem)) {
      handledKernel.insert(prem);
      outKernel.push(prem);
    }
  }

  virtual void printStep(Unit* cs)
  {
    InferenceRule rule;
    UnitIterator parents=_is->getParents(cs, rule);

    cs->inference().updateStatistics(); // in particular, update inductionDepth (which could have decreased, since we might have fewer parents after miniminization)

    // TODO: This does not reflect the way we count applications in Induction
    // since there an entire induction formula resolved is 1 application, here
    // each resolution step counts as one, counting potentially much more
    // switch (rule) {
    //   case InferenceRule::GEN_INDUCTION_HYPERRESOLUTION:
    //     env.statistics->generalizedInductionApplicationInProof++;
    //   case InferenceRule::INDUCTION_HYPERRESOLUTION:
    //     env.statistics->inductionApplicationInProof++;
    //     break;
    //   default:
    //     ;
    // }
    switch (rule) {
      case InferenceRule::STRUCT_INDUCTION_AXIOM_ONE:
      case InferenceRule::STRUCT_INDUCTION_AXIOM_TWO:
      case InferenceRule::STRUCT_INDUCTION_AXIOM_THREE:
      case InferenceRule::STRUCT_INDUCTION_AXIOM_RECURSION:
        env.statistics->structInductionInProof++;
        break;
      case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
      case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
        env.statistics->intInfInductionInProof++;
        break;
      case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
      case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
        env.statistics->intFinInductionInProof++;
        break;
      case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
        env.statistics->intDBInductionInProof++;
        break;
      default:
        ;
    }
    switch (rule) {
      case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
        env.statistics->intInfUpInductionInProof++;
        break;
      case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
        env.statistics->intInfDownInductionInProof++;
        break;
      case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
        env.statistics->intFinUpInductionInProof++;
        break;
      case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
        env.statistics->intFinDownInductionInProof++;
        break;
      case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
        env.statistics->intDBUpInductionInProof++;
        break;
      case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
        env.statistics->intDBDownInductionInProof++;
        break;
      default:
        ;
    }

    if (cs->isClause()) {
      Clause* cl=cs->asClause();
      out << cl->toString() << vstring("\n");
    }
    else {
      out << _is->getUnitIdStr(cs) << ". ";
      FormulaUnit* fu=static_cast<FormulaUnit*>(cs);
      if (env.colorUsed && fu->inheritedColor() != COLOR_INVALID) {
        out << " IC" << fu->inheritedColor() << " ";
      }
      out << fu->formula()->toString() << ' ';

      out <<"["<<Kernel::ruleName(rule);

      if (outputAxiomNames && rule==InferenceRule::INPUT) {
        ASS(!parents.hasNext()); //input clauses don't have parents
        vstring name;
        if (Parse::TPTP::findAxiomName(cs, name)) {
          out << " " << name;
        }
      }

      bool first=true;
      while(parents.hasNext()) {
        Unit* prem=parents.next();
        out << (first ? ' ' : ',');
        out << _is->getUnitIdStr(prem);
        first=false;
      }
      out << "]" << endl;
    }
  }

  void handleStep(Unit* cs)
  {
    InferenceRule rule;
    UnitIterator parents=_is->getParents(cs, rule);

    while(parents.hasNext()) {
      Unit* prem=parents.next();
      ASS(prem!=cs);
      requestProofStep(prem);
    }

    if (!hideProofStep(rule)) {
      if(delayPrinting) delayed.push(cs);
      else printStep(cs);
    }
  }

  void printDelayed()
  {
    // Sort
    sort<UnitNumberComparator>(delayed.begin(),delayed.end());

    // Print
    for(unsigned i=0;i<delayed.size();i++){
      printStep(delayed[i]);
    }

  }



  Stack<Unit*> outKernel;
  Set<Unit*> handledKernel; // use UnitSpec to provide its own hash and equals
  Stack<Unit*> delayed;

  InferenceStore* _is;
  ostream& out;

  bool outputAxiomNames;
  bool delayPrinting;
};

struct InferenceStore::ProofPropertyPrinter
: public InferenceStore::ProofPrinter
{
  ProofPropertyPrinter(ostream& out, InferenceStore* is) : ProofPrinter(out,is)
  {
    max_theory_clause_depth = 0;
    for(unsigned i=0;i<11;i++){ buckets.push(0); }
    last_one = false;
  }

  void print()
  {
    ProofPrinter::print();
    for(unsigned i=0;i<11;i++){ out << buckets[i] << " ";}
    out << endl;
    if(last_one){ out << "yes" << endl; }
    else{ out << "no" << endl; }
  }

protected:

  void printStep(Unit* us)
  {
    static unsigned lastP = Unit::getLastParsingNumber();
    static float chunk = lastP / 10.0;
    if(us->number() <= lastP){
      if(us->number() == lastP){ 
        last_one = true;
      }
      unsigned bucket = (unsigned)(us->number() / chunk);
      buckets[bucket]++;
    }

    // TODO we could make clauses track this information, but I am not sure that that's worth it
    if(us->isClause() && us->isPureTheoryDescendant()){
      //cout << "HERE with " << us->toString() << endl;
      Inference* inf = &us->inference();
      while(inf->rule() == InferenceRule::EVALUATION){
        Inference::Iterator piit = inf->iterator();
        inf = &inf->next(piit)->inference();
      }
      Stack<Inference*> current;
      current.push(inf);
      unsigned level = 0;
      while(!current.isEmpty()){
        //cout << current.size() << endl;
        Stack<Inference*> next;
        Stack<Inference*>::Iterator it(current);
        while(it.hasNext()){
          Inference* inf = it.next();
          Inference::Iterator iit=inf->iterator();
          while(inf->hasNext(iit)) {
            Unit* premUnit=inf->next(iit);
            Inference* premInf = &premUnit->inference();
            while(premInf->rule() == InferenceRule::EVALUATION){
              Inference::Iterator piit = premInf->iterator();
              premUnit = premInf->next(piit);
              premInf = &premUnit->inference();
            }

//for(unsigned i=0;i<level;i++){ cout << ">";}; cout << premUnit->toString() << endl;
            next.push(premInf);
          }
        }
        level++;
        current = next;
      }
      level--;
      //cout << "level is " << level << endl;
      
      if(level > max_theory_clause_depth){
        max_theory_clause_depth=level;
      }
    }
  }

  unsigned max_theory_clause_depth;
  bool last_one;
  Stack<unsigned> buckets;

};


struct InferenceStore::TPTPProofPrinter
: public InferenceStore::ProofPrinter
{
  TPTPProofPrinter(ostream& out, InferenceStore* is)
  : ProofPrinter(out, is) {
    splitPrefix = Saturation::Splitter::splPrefix; 
    // Don't delay printing in TPTP proof mode
    delayPrinting = false;
  }

  void print()
  {
    //outputSymbolDeclarations also deals with sorts for now
    //UIHelper::outputSortDeclarations(out);
    UIHelper::outputSymbolDeclarations(out);
    ProofPrinter::print();
  }

protected:
  vstring splitPrefix;

  vstring getRole(InferenceRule rule, UnitInputType origin)
  {
    switch(rule) {
    case InferenceRule::INPUT:
      if (origin==UnitInputType::CONJECTURE) {
	return "conjecture";
      }
      else {
	return "axiom";
      }
    case InferenceRule::NEGATED_CONJECTURE:
      return "negated_conjecture";
    default:
      return "plain";
    }
  }

  vstring tptpRuleName(InferenceRule rule)
  {
    return StringUtils::replaceChar(ruleName(rule), ' ', '_');
  }

  vstring unitIdToTptp(vstring unitId)
  {
    return "f"+unitId;
  }

  vstring tptpUnitId(Unit* us)
  {
    return unitIdToTptp(_is->getUnitIdStr(us));
  }

  vstring tptpDefId(Unit* us)
  {
    return unitIdToTptp(Int::toString(us->number())+"_D");
  }

  vstring splitsToString(SplitSet* splits)
  {
    ASS_G(splits->size(),0);

    if (splits->size()==1) {
      return Saturation::Splitter::getFormulaStringFromName(splits->sval(),true /*negated*/);
    }
    auto sit = splits->iter();
    vstring res("(");
    while(sit.hasNext()) {
      res+= Saturation::Splitter::getFormulaStringFromName(sit.next(),true /*negated*/);
      if (sit.hasNext()) {
	res+=" | ";
      }
    }
    res+=")";
    return res;
  }

  vstring quoteAxiomName(vstring n)
  {
    static vstring allowedFirst("0123456789abcdefghijklmnopqrstuvwxyz");
    const char* allowed="_ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyz";

    if (n.size()==0 || allowedFirst.find(n[0])==vstring::npos ||
	n.find_first_not_of(allowed)!=vstring::npos) {
      n='\''+n+'\'';
    }
    return n;
  }

  vstring getFofString(vstring id, vstring formula, vstring inference, InferenceRule rule, UnitInputType origin=UnitInputType::AXIOM)
  {
    vstring kind = "fof";
    if(env.getMainProblem()->hasNonDefaultSorts()){ kind="tff"; }
    if(env.getMainProblem()->isHigherOrder()){ kind="thf"; }

    return kind+"("+id+","+getRole(rule,origin)+",("+"\n"
	+"  "+formula+"),\n"
	+"  "+inference+").";
  }

  vstring getFormulaString(Unit* us)
  {
    vstring formulaStr;
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

  bool hasNewSymbols(Unit* u) {
    bool res = _is->_introducedSymbols.find(u->number());
    ASS(!res || _is->_introducedSymbols.get(u->number()).isNonEmpty());
    if(!res){
      res = _is->_introducedSplitNames.find(u->number());
    }
    return res;
  }
  vstring getNewSymbols(vstring origin, vstring symStr) {
    return "new_symbols(" + origin + ",[" +symStr + "])";
  }
  /** It is an iterator over SymbolId */
  template<class It>
  vstring getNewSymbols(vstring origin, It symIt) {
    vostringstream symsStr;
    while(symIt.hasNext()) {
      SymbolId sym = symIt.next();
      if (sym.first == SymbolType::FUNC ) {
        symsStr << env.signature->functionName(sym.second);
      } else if (sym.first == SymbolType::PRED){
        symsStr << env.signature->predicateName(sym.second);
      } else {
        symsStr << env.signature->typeConName(sym.second);
      }
      if (symIt.hasNext()) {
        symsStr << ',';
      }
    }
    return getNewSymbols(origin, symsStr.str());
  }
  vstring getNewSymbols(vstring origin, Unit* u) {
    ASS(hasNewSymbols(u));

    if(_is->_introducedSplitNames.find(u->number())){
      return getNewSymbols(origin,_is->_introducedSplitNames.get(u->number()));
    }

    SymbolStack& syms = _is->_introducedSymbols.get(u->number());
    return getNewSymbols(origin, SymbolStack::ConstIterator(syms));
  }

  void printStep(Unit* us)
  {
    InferenceRule rule;
    UnitIterator parents=_is->getParents(us, rule);

    switch(rule) {
    //case Inference::AVATAR_COMPONENT:
    //  printSplittingComponentIntroduction(us);
    //  return;
    case InferenceRule::GENERAL_SPLITTING_COMPONENT:
      printGeneralSplittingComponent(us);
      return;
    case InferenceRule::GENERAL_SPLITTING:
      printSplitting(us);
      return;
    default: ;
    }

    //get vstring representing the formula

    vstring formulaStr=getFormulaString(us);

    //get inference vstring

    vstring inferenceStr;
    if (rule==InferenceRule::INPUT) {
      vstring fileName;
      if (env.options->inputFile()=="") {
	      fileName="unknown";
      }
      else {
	      fileName="'"+env.options->inputFile()+"'";
      }
      vstring axiomName;
      if (!outputAxiomNames || !Parse::TPTP::findAxiomName(us, axiomName)) {
	      axiomName="unknown";
      }
      inferenceStr="file("+fileName+","+quoteAxiomName(axiomName)+")";
    }
    else if (!parents.hasNext()) {
      vstring newSymbolInfo;
      if (hasNewSymbols(us)) {
        vstring newSymbOrigin;
        if (rule == InferenceRule::FUNCTION_DEFINITION ||
          rule == InferenceRule::FOOL_ITE_DEFINITION || rule == InferenceRule::FOOL_LET_DEFINITION ||
          rule == InferenceRule::FOOL_FORMULA_DEFINITION || rule == InferenceRule::FOOL_MATCH_DEFINITION) {
          newSymbOrigin = "definition";
        } else {
          newSymbOrigin = "naming";
        }
	      newSymbolInfo = getNewSymbols(newSymbOrigin,us);
      }
      inferenceStr="introduced("+tptpRuleName(rule)+",["+newSymbolInfo+"])";
    }
    else {
      ASS(parents.hasNext());
      vstring statusStr;
      if (rule==InferenceRule::SKOLEMIZE) {
	      statusStr="status(esa),"+getNewSymbols("skolem",us);
      }

      inferenceStr="inference("+tptpRuleName(rule);

      inferenceStr+=",["+statusStr+"],[";
      bool first=true;
      while(parents.hasNext()) {
        Unit* prem=parents.next();
        if (!first) {
          inferenceStr+=',';
        }
        inferenceStr+=tptpUnitId(prem);
        first=false;
      }
      inferenceStr+="])";
    }

    out<<getFofString(tptpUnitId(us), formulaStr, inferenceStr, rule, us->inputType())<<endl;
  }

  void printSplitting(Unit* us)
  {
    ASS(us->isClause());

    InferenceRule rule;
    UnitIterator parents=_is->getParents(us, rule);
    ASS(rule==InferenceRule::GENERAL_SPLITTING);

    vstring inferenceStr="inference("+tptpRuleName(rule)+",[],[";

    //here we rely on the fact that the base premise is always put as the first premise in
    //GeneralSplitting::apply

    ALWAYS(parents.hasNext());
    Unit* base=parents.next();
    inferenceStr+=tptpUnitId(base);

    ASS(parents.hasNext()); //we always split off at least one component
    while(parents.hasNext()) {
      Unit* comp=parents.next();
      ASS(_is->_splittingNameLiterals.find(comp));
      inferenceStr+=","+tptpDefId(comp);
    }
    inferenceStr+="])";

    out<<getFofString(tptpUnitId(us), getFormulaString(us), inferenceStr, rule)<<endl;
  }

  void printGeneralSplittingComponent(Unit* us)
  {
    ASS(us->isClause());

    InferenceRule rule;
    UnitIterator parents=_is->getParents(us, rule);
    ASS(!parents.hasNext());

    Literal* nameLit=_is->_splittingNameLiterals.get(us); //the name literal must always be stored

    vstring defId=tptpDefId(us);

    out<<getFofString(tptpUnitId(us), getFormulaString(us),
	    "inference("+tptpRuleName(InferenceRule::CLAUSIFY)+",[],["+defId+"])", InferenceRule::CLAUSIFY)<<endl;


    List<unsigned>* nameVars=0;
    VariableIterator vit(nameLit);
    while(vit.hasNext()) {
      unsigned var=vit.next().var();
      ASS(!List<unsigned>::member(var, nameVars)); //each variable appears only once in the naming literal
      List<unsigned>::push(var,nameVars);
    }

    vstring compStr;
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

    compStr=getQuantifiedStr(compOnlyVars, compStr, multiple);
    List<unsigned>::destroy(compOnlyVars);

    vstring defStr=compStr+" <=> "+Literal::complementaryLiteral(nameLit)->toString();
    defStr=getQuantifiedStr(nameVars, defStr);
    List<unsigned>::destroy(nameVars);

    SymbolId nameSymbol = SymbolId(SymbolType::PRED,nameLit->functor());
    vostringstream originStm;
    originStm << "introduced(" << tptpRuleName(rule)
	      << ",[" << getNewSymbols("naming",getSingletonIterator(nameSymbol))
	      << "])";

    out<<getFofString(defId, defStr, originStm.str(), rule)<<endl;
  }

  void printSplittingComponentIntroduction(Unit* us)
  {
    ASS(us->isClause());

    Clause* cl=us->asClause();
    ASS(cl->splits());
    ASS_EQ(cl->splits()->size(),1);

    InferenceRule rule=InferenceRule::AVATAR_COMPONENT;

    vstring defId=tptpDefId(us);
    vstring splitPred = splitsToString(cl->splits());
    vstring defStr=getQuantifiedStr(cl)+" <=> ~"+splitPred;

    out<<getFofString(tptpUnitId(us), getFormulaString(us),
      "inference("+tptpRuleName(InferenceRule::CLAUSIFY)+",[],["+defId+"])", InferenceRule::CLAUSIFY)<<endl;

    vstringstream originStm;
    originStm << "introduced(" << tptpRuleName(rule)
        << ",[" << getNewSymbols("naming",splitPred)
        << "])";

    out<<getFofString(defId, defStr, originStm.str(), rule)<<endl;
  }

};

struct InferenceStore::ProofCheckPrinter
: public InferenceStore::ProofPrinter
{
  ProofCheckPrinter(ostream& out, InferenceStore* is)
  : ProofPrinter(out, is) {}

protected:
  void printStep(Unit* cs)
  {
    InferenceRule rule;
    UnitIterator parents=_is->getParents(cs, rule);

    //outputSymbolDeclarations also deals with sorts for now
    //UIHelper::outputSortDeclarations(out);
    UIHelper::outputSymbolDeclarations(out);

    vstring kind = "fof";
    if(env.getMainProblem()->hasNonDefaultSorts()){ kind="tff"; } 
    if(env.getMainProblem()->isHigherOrder()){ kind="thf"; }

    out << kind
        << "(r"<<_is->getUnitIdStr(cs)
    	<< ",conjecture, "
    	<< getQuantifiedStr(cs)
    	<< " ). %"<<ruleName(rule)<<"\n";

    while(parents.hasNext()) {
      Unit* prem=parents.next();
      out << kind 
        << "(pr"<<_is->getUnitIdStr(prem)
  	<< ",axiom, "
  	<< getQuantifiedStr(prem);
      out << " ).\n";
    }
    out << "%#\n";
  }


  bool hideProofStep(InferenceRule rule)
  {
    switch(rule) {
    case InferenceRule::INPUT:
    case InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case InferenceRule::INEQUALITY_SPLITTING:
    case InferenceRule::SKOLEMIZE:
    case InferenceRule::EQUALITY_PROXY_REPLACEMENT:
    case InferenceRule::EQUALITY_PROXY_AXIOM1:
    case InferenceRule::EQUALITY_PROXY_AXIOM2:
    case InferenceRule::NEGATED_CONJECTURE:
    case InferenceRule::RECTIFY:
    case InferenceRule::FLATTEN:
    case InferenceRule::ENNF:
    case InferenceRule::NNF:
    case InferenceRule::CLAUSIFY:
    case InferenceRule::AVATAR_DEFINITION:
    case InferenceRule::AVATAR_COMPONENT:
    case InferenceRule::AVATAR_REFUTATION:
    case InferenceRule::AVATAR_SPLIT_CLAUSE:
    case InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
    case InferenceRule::FOOL_LET_DEFINITION:
    case InferenceRule::FOOL_ITE_DEFINITION:
    case InferenceRule::FOOL_ELIMINATION:
    case InferenceRule::BOOLEAN_TERM_ENCODING:
    case InferenceRule::CHOICE_AXIOM:
    case InferenceRule::PREDICATE_DEFINITION:
      return true;
    default:
      return false;
    }
  }

  void print()
  {
    ProofPrinter::print();
    out << "%#\n";
  }
};

InferenceStore::ProofPrinter* InferenceStore::createProofPrinter(ostream& out)
{
  switch(env.options->proof()) {
  case Options::Proof::ON:
    return new ProofPrinter(out, this);
  case Options::Proof::PROOFCHECK:
    return new ProofCheckPrinter(out, this);
  case Options::Proof::TPTP:
    return new TPTPProofPrinter(out, this);
  case Options::Proof::PROPERTY:
    return new ProofPropertyPrinter(out,this);
  case Options::Proof::OFF:
    return 0;
  }
  ASSERTION_VIOLATION;
  return 0;
}

/**
 * Output a proof of refutation to out
 *
 *
 */
void InferenceStore::outputUnsatCore(ostream& out, Unit* refutation)
{
  out << "(" << endl;

  Stack<Unit*> todo;
  todo.push(refutation);
  Set<Unit*> visited;
  while(!todo.isEmpty()){

    Unit* u = todo.pop();
    visited.insert(u);

    if(u->inference().rule() ==  InferenceRule::INPUT){
      if(!u->isClause()){
        if(u->getFormula()->hasLabel()){
          vstring label =  u->getFormula()->getLabel();
          out << label << endl;
        }
        else{
          ASS(env.options->ignoreMissingInputsInUnsatCore() || u->getFormula()->hasLabel());
          if(!(env.options->ignoreMissingInputsInUnsatCore() || u->getFormula()->hasLabel())){
            cout << "ERROR: There is a problem with the unsat core. There is an input formula in the proof" <<  endl;
            cout << "that does not have a label. We expect all  input formulas to have labels as this  is what" << endl;
            cout << "smtcomp does. If you don't want this then use the ignore_missing_inputs_in_unsat_core option" << endl;
            cout << "The unlabelled  input formula is " << endl;
            cout << u->toString() << endl;
          }
        }
      }
      else{
        //Currently ignore clauses as they cannot come from SMT-LIB as input formulas
      }
    }
    else{
      InferenceRule rule;
      UnitIterator parents = InferenceStore::instance()->getParents(u,rule);
      while(parents.hasNext()){
        Unit* parent = parents.next();
        if(!visited.contains(parent)){
          todo.push(parent);
        }
      }
    }
  }

  out << ")" << endl;
}



/**
 * Output a proof of refutation to out
 *
 *
 */
void InferenceStore::outputProof(ostream& out, Unit* refutation)
{
  ProofPrinter* p = createProofPrinter(out);
  if (!p) {
    return;
  }
  ScopedPtr<ProofPrinter> pp(p);
  pp->scheduleForPrinting(refutation);
  pp->print();
}

/**
 * Output a proof of units to out
 *
 */
void InferenceStore::outputProof(ostream& out, UnitList* units)
{
  ProofPrinter* p = createProofPrinter(out);
  if (!p) {
    return;
  }
  ScopedPtr<ProofPrinter> pp(p);
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    pp->scheduleForPrinting(u);
  }
  pp->print();
}

InferenceStore* InferenceStore::instance()
{
  static ScopedPtr<InferenceStore> inst(new InferenceStore());
  
  return inst.ptr();
}

}
