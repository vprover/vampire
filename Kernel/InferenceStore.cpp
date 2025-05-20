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

#include "Kernel/Theory.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/StringUtils.hpp"
#include "Lib/ScopedPtr.hpp"

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
#include "Kernel/NumTraits.hpp"

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
void InferenceStore::recordIntroducedSplitName(Unit* u, std::string name)
{
  ALWAYS(_introducedSplitNames.insert(u->number(),name));
}

/**
 * Return @b inner quantified over variables in @b vars
 *
 * It is caller's responsibility to ensure that variables in @b vars are unique.
 */
template<typename VarContainer>
std::string getQuantifiedStr(const VarContainer& vars, std::string inner, DHMap<unsigned,TermList>& t_map, bool innerParentheses=true){
  VirtualIterator<unsigned> vit=pvi( getContentIterator(vars) );
  std::string varStr;
  bool first=true;
  while(vit.hasNext()) {
    unsigned var =vit.next();
    std::string ty="";
    TermList t;

    if(t_map.find(var,t) && env.getMainProblem()->hasNonDefaultSorts()){
      //hasNonDefaultSorts is true if the problem contains a sort
      //that is not $i and not a variable
      ty=" : " + t.toString();
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

/**
 * Return @b inner quentified over variables in @b vars
 *
 * It is caller's responsibility to ensure that variables in @b vars are unique.
 */
template<typename VarContainer>
std::string getQuantifiedStr(const VarContainer& vars, std::string inner, bool innerParentheses=true)
{
  static DHMap<unsigned,TermList> d;
  return getQuantifiedStr(vars,inner,d,innerParentheses);
}

/**
 * Return std::string containing quantified unit @b u.
 */
std::string getQuantifiedStr(Unit* u, List<unsigned>* nonQuantified=0)
{
  Set<unsigned> vars;
  std::string res;
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

struct InferenceStore::ProofPrinter
{
  ProofPrinter(std::ostream& out, InferenceStore* is)
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
    if (cs->isClause()) {
      Clause* cl=cs->asClause();
      out << cl->toString() << "\n";
    } else {
      InferenceRule rule = cs->inference().rule();
      UnitIterator parents= cs->getParents();

      out << cs->number() << ". ";
      FormulaUnit* fu=static_cast<FormulaUnit*>(cs);
      if (env.colorUsed && fu->inheritedColor() != COLOR_INVALID) {
        out << " IC" << fu->inheritedColor() << " ";
      }
      out << fu->formula()->toString() << ' ';

      out <<"["<<cs->inference().name();

      if (outputAxiomNames && rule==InferenceRule::INPUT) {
        ASS(!parents.hasNext()); //input clauses don't have parents
        std::string name;
        if (Parse::TPTP::findAxiomName(cs, name)) {
          out << " " << name;
        }
      }

      bool first=true;
      while(parents.hasNext()) {
        Unit* prem=parents.next();
        out << (first ? ' ' : ',');
        out << prem->number();
        first=false;
      }

      if(env.options->proofExtra() == Options::ProofExtra::FULL) {
        auto *extra = env.proofExtra.find(cs);
        if(extra)
          out
            << (first ? ' ' : ',')
            << *extra;
      }

      out << "]" << endl;
    }
  }

  void handleStep(Unit* cs)
  {
    InferenceRule rule = cs->inference().rule();
    UnitIterator parents= cs->getParents();

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
    sort(
      delayed.begin(), delayed.end(),
      [](Unit *u1, Unit *u2) -> bool { return u1->number() < u2->number(); }
    );

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
  ProofPropertyPrinter(std::ostream& out, InferenceStore* is) : ProofPrinter(out,is)
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
  TPTPProofPrinter(std::ostream& out, InferenceStore* is)
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
  std::string splitPrefix;

  std::string getRole(InferenceRule rule, UnitInputType origin)
  {
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
    default:
      return "plain";
    }
  }

  std::string tptpRuleName(InferenceRule rule)
  {
    return StringUtils::replaceChar(ruleName(rule), ' ', '_');
  }

  std::string unitIdToTptp(std::string unitId)
  {
    return "f"+unitId;
  }

  std::string tptpUnitId(Unit* us)
  {
    return unitIdToTptp(Int::toString(us->number()));
  }

  std::string tptpDefId(Unit* us)
  {
    return unitIdToTptp(Int::toString(us->number())+"_D");
  }

  std::string splitsToString(SplitSet* splits)
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

  std::string quoteAxiomName(std::string n)
  {
    static std::string allowedFirst("0123456789abcdefghijklmnopqrstuvwxyz");
    const char* allowed="_ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyz";

    if (n.size()==0 || allowedFirst.find(n[0])==std::string::npos ||
	n.find_first_not_of(allowed)!=std::string::npos) {
      n='\''+n+'\'';
    }
    return n;
  }

  std::string getFofString(std::string id, std::string formula, std::string inference, InferenceRule rule, UnitInputType origin=UnitInputType::AXIOM)
  {
    std::string kind = "fof";
    if(env.getMainProblem()->hasNonDefaultSorts()){ kind="tff"; }
    if(env.getMainProblem()->isHigherOrder()){ kind="thf"; }

    return kind+"("+id+","+getRole(rule,origin)+",("+"\n"
	+"  "+formula+"),\n"
	+"  "+inference+").";
  }

  std::string getFormulaString(Unit* us)
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

  bool hasNewSymbols(Unit* u) {
    bool res = _is->_introducedSymbols.find(u->number());
    ASS(!res || _is->_introducedSymbols.get(u->number()).isNonEmpty());
    if(!res){
      res = _is->_introducedSplitNames.find(u->number());
    }
    return res;
  }
  std::string getNewSymbols(std::string origin, std::string symStr) {
    return "new_symbols(" + origin + ",[" +symStr + "])";
  }
  /** It is an iterator over SymbolId */
  template<class It>
  std::string getNewSymbols(std::string origin, It symIt) {
    std::ostringstream symsStr;
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
  std::string getNewSymbols(std::string origin, Unit* u) {
    ASS(hasNewSymbols(u));

    if(_is->_introducedSplitNames.find(u->number())){
      return getNewSymbols(origin,_is->_introducedSplitNames.get(u->number()));
    }

    SymbolStack& syms = _is->_introducedSymbols.get(u->number());
    return getNewSymbols(origin, SymbolStack::ConstIterator(syms));
  }

  void printStep(Unit* us)
  {
    InferenceRule rule = us->inference().rule();
    UnitIterator parents= us->getParents();

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

    //get std::string representing the formula

    std::string formulaStr=getFormulaString(us);

    //get inference std::string

    std::string inferenceStr;
    if (rule==InferenceRule::INPUT) {
      std::string fileName;
      if (env.options->inputFile()=="") {
	      fileName="unknown";
      }
      else {
	      fileName="'"+env.options->inputFile()+"'";
      }
      std::string axiomName;
      if (!outputAxiomNames || !Parse::TPTP::findAxiomName(us, axiomName)) {
        // Giles' ucore extraction code parses labels from smtlib files, let's try printing these too
        if (!us->isClause() && us->getFormula()->hasLabel()) {
          axiomName = us->getFormula()->getLabel();
        } else {
	        axiomName="unknown";
        }
      }
      inferenceStr="file("+fileName+","+quoteAxiomName(axiomName)+")";
    }
    else if (!parents.hasNext()) {
      std::string newSymbolInfo;
      if (hasNewSymbols(us)) {
        std::string newSymbOrigin;
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
      std::string statusStr;
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
      ASS(_is->_splittingNameLiterals.find(comp));
      inferenceStr+=","+tptpDefId(comp);
    }
    inferenceStr+="])";

    out<<getFofString(tptpUnitId(us), getFormulaString(us), inferenceStr, rule)<<endl;
  }

  void printGeneralSplittingComponent(Unit* us)
  {
    ASS(us->isClause());

    InferenceRule rule = us->inference().rule();
    UnitIterator parents= us->getParents();
    ASS(!parents.hasNext());

    Literal* nameLit=_is->_splittingNameLiterals.get(us); //the name literal must always be stored

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

    compStr=getQuantifiedStr(compOnlyVars, compStr, multiple);
    List<unsigned>::destroy(compOnlyVars);

    std::string defStr=compStr+" <=> "+Literal::complementaryLiteral(nameLit)->toString();
    defStr=getQuantifiedStr(nameVars, defStr);
    List<unsigned>::destroy(nameVars);

    SymbolId nameSymbol = SymbolId(SymbolType::PRED,nameLit->functor());
    std::ostringstream originStm;
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

    std::string defId=tptpDefId(us);
    std::string splitPred = splitsToString(cl->splits());
    std::string defStr=getQuantifiedStr(cl)+" <=> ~"+splitPred;

    out<<getFofString(tptpUnitId(us), getFormulaString(us),
      "inference("+tptpRuleName(InferenceRule::CLAUSIFY)+",[],["+defId+"])", InferenceRule::CLAUSIFY)<<endl;

    std::stringstream originStm;
    originStm << "introduced(" << tptpRuleName(rule)
        << ",[" << getNewSymbols("naming",splitPred)
        << "])";

    out<<getFofString(defId, defStr, originStm.str(), rule)<<endl;
  }

};

struct InferenceStore::ProofCheckPrinter
: public InferenceStore::ProofPrinter
{
  ProofCheckPrinter(std::ostream& out, InferenceStore* is)
  : ProofPrinter(out, is) {}

protected:
  void printStep(Unit* cs)
  {
    InferenceRule rule = cs->inference().rule();
    UnitIterator parents= cs->getParents();

    //outputSymbolDeclarations also deals with sorts for now
    //UIHelper::outputSortDeclarations(out);
    UIHelper::outputSymbolDeclarations(out);

    std::string kind = "fof";
    if(env.getMainProblem()->hasNonDefaultSorts()){ kind="tff"; }
    if(env.getMainProblem()->isHigherOrder()){ kind="thf"; }

    out << kind
        << "(r"<< cs->number()
    	<< ",conjecture, "
    	<< getQuantifiedStr(cs)
    	<< " ). %"<<ruleName(rule)<<"\n";

    while(parents.hasNext()) {
      Unit* prem=parents.next();
      out << kind
        << "(pr"<<prem->number()
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
struct InferenceStore::Smt2ProofCheckPrinter
: public InferenceStore::ProofPrinter
{
  USE_ALLOCATOR(InferenceStore::Smt2ProofCheckPrinter);
  
  Smt2ProofCheckPrinter(std::ostream& out, InferenceStore* is)
  : ProofPrinter(out, is) {}

protected:

  static bool isBuiltInSort(std::ostream& out, unsigned sortCons) {
    auto& sig = *env.signature;
    auto arity = sig.typeConArity(sortCons);
    auto args = range(0, arity)
              .map([](auto _a) { return AtomicSort::intSort(); })
              .template collect<Stack>();
    auto sortInstance = TermList(AtomicSort::create(sortCons, arity, args.begin()));
    if (env.signature->isTermAlgebraSort(sortInstance)) {
      out << "=== warning term algebras are not yet implemented for proof checking ==" << std::endl;
    }
    return sig.isArrayCon(sortCons)
      || sortInstance == AtomicSort::intSort()
      || sortInstance == AtomicSort::realSort()
      || sortInstance == AtomicSort::rationalSort();
  }

  static void outputSymbolDeclarations(std::ostream& out)
  {
    auto& sig = *env.signature;

    for (unsigned i=0; i < sig.typeCons(); ++i) {
      if (!isBuiltInSort(/* may output warning */ out, i)) {
        out << "(declare-sort ";
        outputQuoted(out, sig.typeConName(i));
        out << " "
            << sig.typeConArity(i) << ")" 
            << std::endl;
      }
    }
    for (unsigned i = 0; i < sig.functions(); ++i) {
      if ( env.signature->isFoolConstantSymbol(true,i) 
        || env.signature->isFoolConstantSymbol(false,i)
        || forAnyNumTraits([&](auto n) { return env.signature->tryLinMul<typename decltype(n)::ConstantType>(i); })
        || theory->isInterpretedFunction(i)
        || theory->isInterpretedConstant(i))  {
        /* don't output */
      } else {
        out << "(declare-fun ";
        outputFunctionName(out, i);
        out << " (";
        auto fty = sig.getFunction(i)->fnType();
        for (auto a : range(0, sig.functionArity(i))) {
          out << " ";
          outputSort(out, fty->arg(a));
        }
        out << " )";
        outputSort(out, fty->result());
        out << ")" 
            << std::endl;
      }
    }
    for (unsigned i = 0; i < sig.predicates(); ++i) {
      auto fty = sig.getPredicate(i)->predType();
      // we might introduce an equality proxy for rationals, which 
      // we cannot translate to smt2 as there are no rationals there
      // therefore we skip that
      auto hasRatArg = range(0, sig.predicateArity(i))
          .any([&](auto a)
              { return fty->arg(a) == AtomicSort::rationalSort(); });
      if (!theory->isInterpretedPredicate(i) && !hasRatArg) {

        out << "(declare-fun ";
        outputPredicateName(out, i);
        out << " (";
        for (auto a : range(0, sig.predicateArity(i))) {
          out << " ";
          auto s = fty->arg(a);
          outputSort(out, s);
        }
        out << " ) Bool)"
            << std::endl;
      }
    }

    out   << "(define-fun |$floor| ((x Real)) Real " << std::endl
          << "   (to_real (to_int x)))             " << std::endl
          <<                                            std::endl;

    auto defRemainderInTermsOfQuotient = [&](auto kind, auto definition) {
      out << "(declare-fun |$quotient_"  << kind << "0| (Int) Int)         " << std::endl
          << "(declare-fun |$remainder_" << kind << "0| (Int) Int)         " << std::endl
          <<                                                                    std::endl
          << "(define-fun |$quotient_" << kind << "| ((m Int) (n Int)) Int " << std::endl
          << "   (ite (= n 0)                                              " << std::endl
          << "     (|$quotient_" << kind << "0| m)                         " << std::endl
          << definition 
          << "   )"                                                          << std::endl
          << ")"                                                             << std::endl
          <<                                                                    std::endl
          << "(define-fun |$remainder_" << kind << "| ((m Int) (n Int)) Int" << std::endl
          << "   (ite (= n 0)                                              " << std::endl
          << "    (|$remainder_" << kind << "0| m)                         " << std::endl
          << "    (- m (* n (|$quotient_" << kind << "| m n)))))           " << std::endl;
    };

    defRemainderInTermsOfQuotient("f",
           // definition: floor( m/n)
           //           = -ceil(-m/n)
           //
           // smtlib standard for div:
           // Regardless of sign of m, 
           // when n is positive, (div m n) is the floor of the rational number m/n;
           // when n is negative, (div m n) is the ceiling of m/n.
           "    (ite (> n 0)                            \n"
           //       n > 0 => div(m,n) = floor(m/n)
           "        (div m n)                           \n"
           //       n < 0 =>  div(-m,n) =  ceil(-m/n)
           //             => -div(-m,n) = -ceil(-m/n)
           //             => -div(-m,n) =   floor(m/n)
           "        (-(div (- m) n))                      \n"
           "    )                                       \n"
           );


    defRemainderInTermsOfQuotient("t",
           // definition: truncate(m/n)
           //          = if (m/n > 0) floor(m/n)
           //            else         ceil(m/n)
           // smtlib standard for div:
           // Regardless of sign of m, 
           // when n is positive, (div m n) is the floor of the rational number m/n;
           // when n is negative, (div m n) is the ceiling of m/n.
           "    (ite (> n 0)                             \n"
           "       (ite (> m 0)                             \n"
           //            m/n > 0 => we need floor(m/n)
           //                    => n is potitive
           //                    => div(m, n) = floor(m/n)
           "            (div m n)                           \n"
           //            m/n <= 0 => we need ceiling(m/n)
           //                     => -n is negativ
           //                     => div(-m,-n) = floor(-m/-n)
           "            (div (- m) (- n))                   \n"
           "       )                                        \n"
           "       (ite (> m 0)                             \n"
           //            m/n < 0 => we need ceiling(m/n)
           //                    => n is negative
           //                    => div(m, n) = ceil(m/n)
           "            (div m n)                           \n"
           //            m/n > 0 => we need floor(m/n)
           //                    => -n is positive
           //                    => div(-m, -n) = floor(-m / -n)
           "            (div (- m) (- n))                   \n"
           "       )                                        \n"
           "    )                                           \n");


  }

  static void outputVar(std::ostream& out, unsigned var)
  { out << "x" << var; }


#define INTERPRETATION_BY_TRANSLATION                                                     \
           Theory::INT_QUOTIENT_T:                                                        \
      case Theory::INT_QUOTIENT_F:                                                        \
      case Theory::REAL_FLOOR:                                                            \
      case Theory::RAT_FLOOR:                                                             \
      case Theory::INT_REMAINDER_T:                                                       \
      case Theory::INT_REMAINDER_F


#define ALL_NUM(SUFFIX)                                                                   \
           Theory::INT_ ## SUFFIX:                                                        \
      case Theory::RAT_ ## SUFFIX:                                                        \
      case Theory::REAL_ ## SUFFIX


#define UNSUPPORTED_INTERPRETATIONS                                                       \
           Theory::RAT_IS_RAT:                                                            \
      case Theory::RAT_IS_REAL:                                                           \
      case Theory::REAL_IS_RAT:                                                           \
      case Theory::REAL_IS_REAL:                                                          \
      case Theory::INT_DIVIDES:                                                           \
      case Theory::INT_CEILING:                                                           \
      case Theory::INT_TRUNCATE:                                                          \
      case Theory::INT_ROUND:                                                             \
      case Theory::RAT_QUOTIENT:                                                          \
      case Theory::RAT_QUOTIENT_E:                                                        \
      case Theory::RAT_QUOTIENT_T:                                                        \
      case Theory::RAT_QUOTIENT_F:                                                        \
      case Theory::RAT_REMAINDER_E:                                                       \
      case Theory::RAT_REMAINDER_T:                                                       \
      case Theory::RAT_REMAINDER_F:                                                       \
      case Theory::RAT_CEILING:                                                           \
      case Theory::RAT_TRUNCATE:                                                          \
      case Theory::RAT_ROUND:                                                             \
      case Theory::REAL_QUOTIENT_E:                                                       \
      case Theory::REAL_QUOTIENT_T:                                                       \
      case Theory::REAL_QUOTIENT_F:                                                       \
      case Theory::REAL_REMAINDER_E:                                                      \
      case Theory::REAL_REMAINDER_T:                                                      \
      case Theory::REAL_REMAINDER_F:                                                      \
      case Theory::REAL_CEILING:                                                          \
      case Theory::REAL_TRUNCATE:                                                         \
      case Theory::REAL_ROUND:                                                            \
      case Theory::RAT_TO_RAT:                                                            \
      case Theory::REAL_TO_RAT:                                                           \
      case Theory::INT_IS_RAT:                                                            \
      case Theory::INT_IS_REAL:                                                           \
      case Theory::INT_TO_RAT

  static void outputInterpretationName(std::ostream& out, Theory::Interpretation itp) 
  {

    switch (itp) {
      case ALL_NUM(IS_INT):        out << "is_int";  return;
      case ALL_NUM(TO_REAL):       out << "to_real"; return;
      case ALL_NUM(TO_INT):        out << "to_int";  return;
      case ALL_NUM(GREATER):       out << ">";       return;
      case ALL_NUM(GREATER_EQUAL): out << ">=";      return;
      case ALL_NUM(LESS):          out << "<";       return;
      case ALL_NUM(LESS_EQUAL):    out << "<=";      return;
      case ALL_NUM(PLUS):          out << "+";       return;
      case ALL_NUM(MINUS):         out << "-";       return;
      case ALL_NUM(UNARY_MINUS):   out << "-";       return;
      case ALL_NUM(MULTIPLY):      out << "*";       return;
      case Theory::RAT_FLOOR:      out << "|$floor|";       return;
      case Theory::REAL_FLOOR:     out << "|$floor|";       return;

      case Theory::EQUAL: out << "="; return;

      case UNSUPPORTED_INTERPRETATIONS:
         throw UserErrorException("divides function ", itp, " does not exist in SMT2");

      case Theory::INT_SUCCESSOR: out << "+ 1"; return;
      case Theory::INT_ABS: out << "abs"; return;

      case Theory::INT_QUOTIENT_E: out << "div"; return;
      case Theory::INT_REMAINDER_E: out << "mod"; return;

      case Theory::INT_QUOTIENT_T:  out << "|$quotient_t|"; return;
      case Theory::INT_REMAINDER_T: out << "|$remainder_t|"; return;

      case Theory::INT_QUOTIENT_F:  out << "|$quotient_f|"; return;
      case Theory::INT_REMAINDER_F: out << "|$remainder_f|"; return;

      case Theory::INT_FLOOR: out << "to_int"; return;

      case Theory::REAL_QUOTIENT: out << "/"; return;

      // array functions
      case Theory::ARRAY_BOOL_SELECT:
      case Theory::ARRAY_SELECT: out << "select"; return;
      case Theory::ARRAY_STORE: out << "store"; return;

      case Theory::INVALID_INTERPRETATION: {ASSERTION_VIOLATION}
    }
    ASSERTION_VIOLATION


  }


  static void outputPredicateName(std::ostream& out, unsigned p) 
  {
    if (theory->isInterpretedPredicate(p)) {
      outputInterpretationName(out, theory->interpretPredicate(p));
    } else {
      outputQuoted(out, env.signature->predicateName(p));
    }
  }

  static void outputQuoted(std::ostream& out, std::string const& name) 
  {
    if (   name == "exp"
        || name == "log"
        || name == "cos"
        || name == "sin"
        || name == "tan"
        || name == "sqrt"
        || name == "const"
        ) {
        out << "_" << name;
    } else if ( name[0] == '\'' || name[0] == '$') {
      // add one more level of quoting
      out << '|' << name << "|";
    } else  {
      out << name;
    }
  }

  static void outputNumeral(std::ostream& out, IntegerConstantType const& n) {
    if (n < IntegerConstantType(0)) {
      out << "(- " << n.abs() << ")";
    } else {
      out << n;
    }
  }

  static void outputNumeral(std::ostream& out, RationalConstantType const& r) {
    throw UserErrorException("only reals and integers are allowed in smt2");
  }

  static void outputNumeral(std::ostream& out, RealConstantType const& r) {
    if (r < 0) {
      out << "(- ";
    }
    if (r.denominator() == 1) {
      out << r.numerator().abs() << ".0";
    } else {
      out << "(/ " << r.numerator().abs() << ".0 " << r.denominator() << ".0)";
    }
    if (r < 0) {
      out << ")";
    }
  }

  static void outputFunctionName(std::ostream& out, unsigned f) 
  {
    auto linMulOutputted = forAnyNumTraits([&](auto n) { 
        if (auto num = env.signature->tryLinMul<typename decltype(n)::ConstantType>(f)) {
          out << "* ";
          outputNumeral(out, *num);
          return true;
        } else {
          return false; 
        }
    });
    if (linMulOutputted) return;

    auto numeralOutputted = forAnyNumTraits([&](auto n) { 
       typename decltype(n)::ConstantType num;
       if (theory->tryInterpretConstant(f, num)) {
         outputNumeral(out, num);
         return true;
       } else {
         return false;
       }
    });
    if (numeralOutputted) return;

    if (theory->isInterpretedFunction(f)) {
      outputInterpretationName(out, theory->interpretFunction(f));
        
    } else if (env.signature->isFoolConstantSymbol(true, f)) {
      out << "true";

    } else if (env.signature->isFoolConstantSymbol(false, f)) {
      out << "false";

    } else {
      auto& name = env.signature->functionName(f);
      outputQuoted(out, name);
    }
  }


#define DIRECT_SMT2_INTERPRETATION                                                        \
            Theory::EQUAL:                                                                \
      case ALL_NUM(IS_INT):                                                               \
      case ALL_NUM(TO_REAL):                                                              \
      case ALL_NUM(TO_INT):                                                               \
      case ALL_NUM(GREATER):                                                              \
      case ALL_NUM(GREATER_EQUAL):                                                        \
      case ALL_NUM(LESS):                                                                 \
      case ALL_NUM(LESS_EQUAL):                                                           \
      case ALL_NUM(PLUS):                                                                 \
      case ALL_NUM(MINUS):                                                                \
      case ALL_NUM(UNARY_MINUS):                                                          \
      case ALL_NUM(MULTIPLY):                                                             \
      case Theory::INT_SUCCESSOR:                                                         \
      case Theory::INT_ABS:                                                               \
      case Theory::INT_QUOTIENT_E:                                                        \
      case Theory::INT_REMAINDER_E:                                                       \
      case Theory::INT_FLOOR:                                                             \
      case Theory::REAL_QUOTIENT:                                                         \
      case Theory::ARRAY_BOOL_SELECT:                                                     \
      case Theory::ARRAY_SELECT:                                                          \
      case Theory::ARRAY_STORE


  bool isInterpretedByTranslation(Term* t)
  {
    if (theory->isInterpretedFunction(t)) {
      switch (theory->interpretFunction(t)) {
        case INTERPRETATION_BY_TRANSLATION:
          return true;
        default:
          return false;
      }
    } else {
      return false;
    }
  }

  static void outputAppl(std::ostream& out, Term* t)
  {

    if (t->isSpecial()) {
      auto f = t->specialFunctor();
      const Term::SpecialTermData* sd = t->getSpecialData();
      switch(f) {
        case SpecialFunctor::FORMULA: outputFormula(out, sd->getFormula()); return;
        case SpecialFunctor::LET: {
          out << "(let ((";
          VList* variables = sd->getVariables();
          if (VList::isNonEmpty(variables)) 
            throw UserErrorException("bindings with variables are not supperted in smt2 proofcheck");

          auto binding = sd->getBinding();
          bool isPredicate = binding.isTerm() && binding.term()->isBoolean();

          out << "?";
          if (isPredicate) {
            outputPredicateName(out, sd->getFunctor());
          } else {
            outputFunctionName(out, sd->getFunctor());
          }
          out << " ";
          outputTerm(out, binding);
          out << "))";
          ASS_EQ(t->numTermArguments(), 1)
          outputTerm(out, t->termArg(0));
          out << ")";
          return;
        }

        case SpecialFunctor::ITE: {
          out << "(ite ";
          outputFormula(out, sd->getCondition());
          ASS_EQ(t->numTermArguments(), 2)
          outputTerm(out, t->termArg(0));
          outputTerm(out, t->termArg(1));
          out << ")";
          return;
        }
        case SpecialFunctor::TUPLE: 
            throw UserErrorException("tuples are not supperted in smt2 proofcheck");

        case SpecialFunctor::LAMBDA:
            throw UserErrorException("lambdas are not supperted in smt2 proofcheck");

        case SpecialFunctor::LET_TUPLE: 
            throw UserErrorException("tuples lets are not supperted in smt2 proofcheck");

        case SpecialFunctor::MATCH:
            throw UserErrorException("&match are not supperted in smt2 proofcheck");
      }


    } else {
      // if (isInterpretedByTranslation(t)) {
      //   outputTranslation(out, t);
      //
      // } else {

        if (t->numTermArguments() != 0) {
          out << "(";
        }
        if (t->isLiteral()) {
          outputPredicateName(out, t->functor());
        } else {
          outputFunctionName(out, t->functor());
        }

        for (unsigned i = 0; i < t->numTermArguments(); i++) {
          out << " ";
          outputTerm(out, t->termArg(i));
        }
        if (t->numTermArguments() != 0) {
          out << ")";
        }
      // }
    }
  }


  static void outputLiteral(std::ostream& out, Literal* lit) 
  {
    if (lit->isNegative()) {
      out << "(not ";
    }
    outputAppl(out, lit);
    if (lit->isNegative()) {
      out << ")";
    }
  }
  static void outputTerm(std::ostream& out, TermList t) 
  {
    if (t.isVar()) {
      outputVar(out, t.var());
    } else {
      outputAppl(out, t.term());
    }
  }

  static void outputFormula(std::ostream& out, Formula* f)
  {
    auto outputBin = [&](const char* name) {
      out << "(" << name << " ";
      outputFormula(out, f->left());
      outputFormula(out, f->right());
      out << ")";
    };
    auto outputCon = [&](const char* name) {
      const FormulaList* fs = f->args();
      ASS (FormulaList::length(fs) >= 2);

      out << "(" << name;
      
      while (FormulaList::isNonEmpty(fs)) {
        out << " ";
        outputFormula(out, fs->head());
        fs = fs->tail();
      }
      out << ")";
    };
    auto outputQuant = [&](const char* name) {
      out << "("<< name << "(";
      VList::Iterator vs(f->vars());
      SList::Iterator ss(f->sorts());
      bool hasSorts = f->sorts();
      while (vs.hasNext()) {
        int var = vs.next();
        out << "(";
        outputVar(out, var);
        out << " ";
        TermList sort;
        if (hasSorts) {
          sort = ss.next();
        } else {
          ALWAYS(SortHelper::tryGetVariableSort(var, const_cast<Formula*>(f),sort))
        }
        outputSort(out, sort);
        out << ")";
      }
      out << ")";
      outputFormula(out, f->qarg());
      out << ")";
    };
    switch (f->connective()) {
      case NAME:
        out << static_cast<const NamedFormula*>(f)->name();
        return;

      case LITERAL:
        outputLiteral(out, f->literal());
        return;

      case NOT:
        out << "(not ";
        outputFormula(out, f->uarg());
        out  << ")";
        return;
                 
      case AND: outputCon("and"); return;
      case OR : outputCon("or" ); return;
      case IFF: outputBin("=" ); return;
      case XOR: outputBin("distinct"); return;
      case IMP: outputBin("=>"); return;
      case FORALL: outputQuant("forall"); return;
      case EXISTS: outputQuant("exists"); return;
      case BOOL_TERM: outputTerm(out, f->getBooleanTerm()); return;
      case TRUE: out << "true"; return;
      case FALSE: out << "false"; return;
      case NOCONN: ASSERTION_VIOLATION_REP(*f);
    }
    ASSERTION_VIOLATION_REP(*f)
  }

  static void outputSort(std::ostream& out, TermList sort)
  { 
    ASS(sort.isTerm())
    if (AtomicSort::intSort() == sort) {
      out << "Int"; 
    } else if (AtomicSort::rationalSort() == sort) {
      throw UserErrorException("smtlib2 does not have rational sorts");
    } else if (AtomicSort::realSort() == sort) {
      out << "Real";
    } else if (AtomicSort::boolSort() == sort) {
      out << "Bool";
    } else {
      auto term = sort.term();
      if (term->arity() == 0) {
        outputQuoted(out, env.signature->typeConName(term->functor()));

      } else {
        out << "(";
        if (sort.isArraySort()){
          out << "Array";
        } else {
          outputQuoted(out, env.signature->typeConName(term->functor()));
        }
        for (unsigned a = 0; a < term->arity(); a++) {
           out << " ";
           outputSort(out, *term->nthArgument(a));
        }
        out << ")";
      }
    }
  }

  static void output(std::ostream& out, Unit* unit)
  {
    using Sort = TermList;
    DHMap<unsigned, Sort> vars;
    SortHelper::collectVariableSorts(unit, vars);
    decltype(vars)::Iterator iter(vars);
    if (vars.size() != 0) {
      out << "(forall (";
      while (iter.hasNext()) {
        unsigned var;
        Sort sort;
        iter.next(var, sort);
        out << "(";
        outputVar(out, var);
        out << " ";
        outputSort(out, sort);
        out << ")";
      }
      out << ")";
    }

    if (unit->isClause()) {
      Clause* cl=static_cast<Clause*>(unit);
      out << "(or false " << std::endl;
      for(auto lit : iterTraits(cl->iterLits())) {
        out << "  ";
        outputLiteral(out, lit);
        out << std::endl;
      }
      out << "  )";
    } else {
      outputFormula(out, static_cast<FormulaUnit*>(unit)->formula());
    }


    if (vars.size() != 0) {
      out << ")";
    }
  }

  void printStep(Unit* concl)
  {
    auto prems = iterTraits(concl->getParents());
 
    outputSymbolDeclarations(out);
    out        << std::endl;
    out        << std::endl;

    for (auto prem : prems) {
      out << ";- unit id: " << prem->number() << std::endl;
      out << "(assert ";
      output(out, prem);
      out << ")" << std::endl;
      out        << std::endl;
    }

    out << std::endl;
    out << ";- rule: " << ruleName(concl->inference().rule()) << std::endl;
    out << std::endl;
    out << ";- unit id: " << concl->number() << std::endl;
    out << "(assert (not ";
    output(out, concl);
    out  << "))" << std::endl;

    out << "(check-sat)" << std::endl;
    out << "%#" << std::endl;
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

InferenceStore::ProofPrinter* InferenceStore::createProofPrinter(std::ostream& out)
{
  switch(env.options->proof()) {
  case Options::Proof::ON:
    return new ProofPrinter(out, this);
  case Options::Proof::SMT2_PROOFCHECK:
    return new Smt2ProofCheckPrinter(out, this);
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
void InferenceStore::outputUnsatCore(std::ostream& out, Unit* refutation)
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
          std::string label =  u->getFormula()->getLabel();
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
      UnitIterator parents = u->getParents();
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
void InferenceStore::outputProof(std::ostream& out, Unit* refutation)
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
void InferenceStore::outputProof(std::ostream& out, UnitList* units)
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

#undef ALL_NUM
}
