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

#include "Shell/LaTeX.hpp"
#include "Shell/Options.hpp"

#include "Parse/TPTP.hpp"

#include "BDD.hpp"
#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "FormulaVarIterator.hpp"
#include "Inference.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "InferenceStore.hpp"

//TODO: when we delete clause, we should also delete all its records from the inference store

namespace Kernel
{

using namespace std;
using namespace Lib;
using namespace Shell;

void InferenceStore::FullInference::increasePremiseRefCounters()
{
  CALL("InferenceStore::FullInference::increasePremiseRefCounters");

  for(unsigned i=0;i<premCnt;i++) {
    if (premises[i].isClause()) {
      premises[i].cl()->incRefCnt();
    }
  }
}



InferenceStore::InferenceStore()
: _bdd(BDD::instance())
{
}

string InferenceStore::getUnitIdStr(UnitSpec cs)
{
  CALL("InferenceStore::getUnitIdStr");

  if (!cs.isClause()) {
    return Int::toString(cs.unit()->number());
  }
  string suffix=getClauseIdSuffix(cs);
  if (suffix=="") {
    return Int::toString(cs.cl()->number());
  }
  return Int::toString(cs.cl()->number())+"_"+suffix;
}

string InferenceStore::getClauseIdSuffix(UnitSpec cs)
{
  CALL("InferenceStore::getClauseIdSuffix");

  FullInference* finf;
  if (_data.find(cs,finf)) {
    if (!finf->csId) {
      finf->csId=_nextClIds.insert(cs.cl());
    }
    return Int::toString(finf->csId);
  } else {
    //only clause constant prop. part can miss their Kernel-inference.
    if (_bdd->isTrue(cs.prop())) {
      return "T";
    } else {
      ASS(_bdd->isFalse(cs.prop()));
      return "";
    }
  }
}

void InferenceStore::recordNonPropInference(Clause* cl)
{
  CALL("InferenceStore::recordNonPropInference/1");

  bool nonTrivialProp=!_bdd->isConstant(cl->prop());
  if (!nonTrivialProp) {
    Inference* cinf=cl->inference();
    Inference::Iterator it = cinf->iterator();
    while (cinf->hasNext(it) && !nonTrivialProp) {
      Unit* uPrem = cinf->next(it);
      if (uPrem->isClause()) {
	Clause* prem=static_cast<Clause*>(uPrem);
	if (!_bdd->isFalse(prem->prop())) {
	  nonTrivialProp=true;
	}
      }
      else {
	nonTrivialProp=true;
      }
    }
  }

  if (nonTrivialProp) {
    recordNonPropInference(cl, cl->inference());
  }


}

/**
 * Increase the reference counter on premise clauses and store @c inf as inference
 * of @c unit.
 */
void InferenceStore::recordInference(UnitSpec unit, FullInference* inf)
{
  CALL("InferenceStore::recordInference");

  inf->increasePremiseRefCounters();
  _data.set(unit, inf);
}

void InferenceStore::recordNonPropInference(Clause* cl, Inference* cinf)
{
  CALL("InferenceStore::recordNonPropInference/2");
  ASS(!_bdd->isTrue(cl->prop()));

  static Stack<Unit*> prems(8);
  prems.reset();

  Inference::Iterator it = cinf->iterator();
  while (cinf->hasNext(it)) {
    Unit* prem=cinf->next(it);
    prems.push(prem);
  }

  unsigned premCnt=prems.size();
  FullInference* finf=new (premCnt) FullInference(premCnt);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=UnitSpec(prems[i]);
  }
  finf->rule=cinf->rule();

  recordInference(UnitSpec(cl), finf);
}

void InferenceStore::recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp)
{
  CALL("InferenceStore::recordPropReduce");

  if (_bdd->isTrue(cl->prop())) {
    return;
  }
  recordPropAlter(cl, oldProp, newProp, Inference::PROP_REDUCE);
}

void InferenceStore::recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp,
	Inference::Rule rule)
{
  CALL("InferenceStore::recordPropAlter");
  ASS(!_bdd->isTrue(newProp));

  FullInference* finf=new (1) FullInference(1);
  finf->premises[0]=UnitSpec(cl, oldProp);
  finf->rule=rule;

  recordInference(UnitSpec(cl, newProp), finf);
}

void InferenceStore::recordIntroduction(Clause* cl, BDDNode* prop, Inference::Rule rule)
{
  CALL("InferenceStore::recordIntroduction");
  ASS(!_bdd->isTrue(prop));

  FullInference* finf=new (0) FullInference(0);
  finf->rule=rule;

  recordInference(UnitSpec(cl, prop), finf);
}



void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/4");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=UnitSpec(cl, oldClProp);
  finf->premises[1]=UnitSpec(addedCl);
  finf->rule=Inference::COMMON_NONPROP_MERGE;

  recordInference(UnitSpec(cl, resultProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldProp, BDDNode* addedProp, BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/4");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=UnitSpec(cl, oldProp);
  finf->premises[1]=UnitSpec(cl, addedProp);
  finf->rule=Inference::COMMON_NONPROP_MERGE;

  recordInference(UnitSpec(cl, resultProp), finf);
}


void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, UnitSpec* addedCls, int addedClsCnt,
	BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/5");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (addedClsCnt+1) FullInference(addedClsCnt+1);
  for(int i=0;i<addedClsCnt;i++) {
    finf->premises[i]=addedCls[i];
  }
  finf->premises[addedClsCnt]=UnitSpec(cl, oldClProp);
  finf->rule=Inference::COMMON_NONPROP_MERGE;

  recordInference(UnitSpec(cl, resultProp), finf);
}

/**
 * Records informations needed for outputting proofs of splitting without
 * backtracking that does not use BDDs and of general splitting
 */
void InferenceStore::recordSplittingNameLiteral(UnitSpec us, Literal* lit)
{
  CALL("InferenceStore::recordSplittingNameLiteral");

  //each clause is result of a splitting only once
  ALWAYS(_splittingNameLiterals.insert(us, lit));
}

/**
 * Records informations needed for outputting proofs of splitting without
 * backtracking that uses BDDs
 */
void InferenceStore::recordSplitting(SplittingRecord* srec, unsigned premCnt, UnitSpec* prems)
{
  CALL("InferenceStore::recordSplitting");
  ASS(!_bdd->isTrue(srec->result.prop()));

  FullInference* finf=new (premCnt) FullInference(premCnt);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=prems[i];
  }

  finf->rule=Inference::SPLITTING;

  recordInference(srec->result, finf);

  //There is no need to increase reference counters in splitting premises,
  //as they're stored in the variant index of Splitter object, so won't get
  //deleted.
  _splittingRecords.set(srec->result, srec);
}

/**
 * Record propositional variables introduced in the @b Inference::BDDZATION
 * inference.
 */
void InferenceStore::recordBddizeVars(Clause* cl, IntList* vars)
{
  CALL("InferenceStore::recordBddizeVars");
  ASS(vars);

  ALWAYS(_bddizeVars.insert(cl, vars));
}

void InferenceStore::recordIntroducedSymbol(Unit* u, bool func, unsigned number)
{
  CALL("InferenceStore::recordIntroducedSymbol");

  SymbolStack* pStack;
  _introducedSymbols.getValuePtr(u->number(),pStack);
  pStack->push(SymbolId(func,number));
}

/**
 * Called before a clause is destroyed
 *
 * Deletes all records for the clause @b cl that can be efficiently reached,
 * as the clause is being destroyed and there will be no further need of them.
 */
void InferenceStore::deleteClauseRecords(Clause* cl)
{
  if (!cl->prop()) {
    return;
  }
  UnitSpec cs=UnitSpec(cl);
  if (_data.find(cs)) {
    _data.remove(cs);
  }
}

UnitSpecIterator InferenceStore::getParents(UnitSpec us, Inference::Rule& rule)
{
  CALL("InferenceStore::getParents/2");
  ASS(!us.isEmpty());

  if (us.isPropTautology()) {
    rule=Inference::TAUTOLOGY_INTRODUCTION;
    return VirtualIterator<UnitSpec>::getEmpty();
  }
//  if (us.isClause()) {
  FullInference* finf;
  if (_data.find(us, finf)) {
    rule=finf->rule;
    return pvi( PointerIterator<UnitSpec>(finf->premises, finf->premises+finf->premCnt) );
  }
//  }
  Unit* u=us.unit();
  List<UnitSpec>* res=0;
  Inference* inf=u->inference();
  Inference::Iterator iit=inf->iterator();
  while(inf->hasNext(iit)) {
    Unit* premUnit=inf->next(iit);
    List<UnitSpec>::push(UnitSpec(premUnit, true), res);
  }
  rule=inf->rule();
  res=res->reverse(); //we want items in the same order
  return pvi( List<UnitSpec>::DestructiveIterator(res) );
}

UnitSpecIterator InferenceStore::getParents(UnitSpec us)
{
  CALL("InferenceStore::getParents/1");

  Inference::Rule aux;
  return getParents(us, aux);
}

/**
 * Return @b inner quentified over variables in @b vars
 *
 * It is caller's responsibility to ensure that variables in @b vars are unique.
 */
template<typename VarContainer>
string getQuantifiedStr(const VarContainer& vars, string inner, bool innerParentheses=true)
{
  CALL("getQuantifiedStr(VarContainer, string)");

  VirtualIterator<unsigned> vit=pvi( getContentIterator(vars) );
  string varStr;
  bool first=true;
  while(vit.hasNext()) {
    unsigned var=vit.next();
    if (!first) {
      varStr+=",";
    }
    varStr+=string("X")+Int::toString(var);
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
 * Return string containing quantified unit @b u.
 *
 * If @b u is clause, only non-propositional part of the clause is
 * returned. (BDD part and the split history are ommitted.)
 */
string getQuantifiedStr(Unit* u, List<unsigned>* nonQuantified=0)
{
  CALL("getQuantifiedStr(Unit*...)");

  Set<unsigned> vars;
  string res;
  if (u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      TermVarIterator vit( (*cl)[i] );
      while(vit.hasNext()) {
	unsigned var=vit.next();
	if (nonQuantified->member(var)) {
	  continue;
	}
	vars.insert(var);
      }
    }
    res=cl->nonPropToString();
  } else {
    Formula* formula=static_cast<FormulaUnit*>(u)->formula();
    FormulaVarIterator fvit( formula );
    while(fvit.hasNext()) {
      unsigned var=fvit.next();
      if (nonQuantified->member(var)) {
        continue;
      }
      vars.insert(var);
    }
    res=formula->toString();
  }

  return getQuantifiedStr(vars, res);
}

struct InferenceStore::ProofPrinter
{
  ProofPrinter(ostream& out, InferenceStore* is)
  : _is(is), out(out), bdd(BDD::instance())
  {
    CALL("InferenceStore::ProofPrinter::ProofPrinter");

    outputAxiomNames=env.options->outputAxiomNames();
  }

  void scheduleForPrinting(UnitSpec us)
  {
    CALL("InferenceStore::ProofPrinter::scheduleForPrinting");

    outKernel.push(us);
    handledKernel.insert(us);
  }


  virtual ~ProofPrinter() {}

  virtual void print()
  {
    CALL("InferenceStore::ProofPrinter::print");

    while(outKernel.isNonEmpty()) {
      UnitSpec cs=outKernel.pop();
      bdd->allowDefinitionOutput(false);
      handleStep(cs);
      bdd->allowDefinitionOutput(true);
    }
  }

protected:
  virtual void handleSplitting(SplittingRecord* sr)
  {
    requestProofStep(sr->premise);
    UnitSpec cs=sr->result;
    Clause* cl=cs.cl();
    out << _is->getUnitIdStr(cs) << ". "
	<< cl->nonPropToString();
    if (!bdd->isFalse(cs.prop())) {
      out <<" | "<<bdd->toString(cs.prop());
    }
    out << " ("<<cl->age()<<':'<<cl->weight()<<") ";

    out <<"["<<Inference::ruleName(Inference::SPLITTING)<<" "
      <<_is->getUnitIdStr(sr->premise);

    Stack<pair<int,Clause*> >::Iterator compIt(sr->namedComps);
    while(compIt.hasNext()) {
      out<<","<<compIt.next().second->number()<<"_D";
    }
    out <<"]\n";

    Stack<pair<int,Clause*> >::Iterator compIt2(sr->namedComps);
    while(compIt2.hasNext()) {
      pair<int,Clause*> nrec=compIt2.next();
      out<<nrec.second->number()<<"_D. ";
      if (nrec.second->length()==1 && (*nrec.second)[0]->arity()==0) {
	out<<(*nrec.second)[0]->predicateName();
      } else {
	out<<getQuantifiedStr(nrec.second);
      }
      out<<" <=> ";
      if (nrec.first>0) {
	out<<bdd->getPropositionalPredicateName(nrec.first);
      }
      else {
        out<<"~"<<bdd->getPropositionalPredicateName(-nrec.first);
      }
      out<<" ["<<Inference::ruleName(Inference::SPLITTING_COMPONENT)<<"]\n";
    }
  }

  virtual bool hideProofStep(Inference::Rule rule)
  {
    return false;
  }

  void requestProofStep(UnitSpec prem)
  {
    if (!bdd->isTrue(prem.prop()) && !handledKernel.contains(prem)) {
      handledKernel.insert(prem);
      outKernel.push(prem);
    }
  }

  virtual void printStep(UnitSpec cs)
  {
    Inference::Rule rule;
    UnitSpecIterator parents=_is->getParents(cs, rule);

    out << _is->getUnitIdStr(cs) << ". ";
    if (cs.isClause()) {
      Clause* cl=cs.cl();
      out << cl->nonPropToString();
      if (!bdd->isFalse(cs.prop())) {
  	out << " | "<<bdd->toString(cs.prop());
      }
      if (cl->splits() && !cl->splits()->isEmpty()) {
        out << " {" << cl->splits()->toString() << "}";
      }
      out << " ("<<cl->age()<<':'<<cl->weight()<<") ";
    }
    else {
      ASS(bdd->isFalse(cs.prop()));
      FormulaUnit* fu=static_cast<FormulaUnit*>(cs.unit());
      out << fu->formula()->toString() << ' ';
    }

    out <<"["<<Inference::ruleName(rule);

    if (outputAxiomNames && rule==Inference::INPUT) {
      ASS(!parents.hasNext()); //input clauses don't have parents
      string name;
      if (Parse::TPTP::findAxiomName(cs.unit(), name)) {
	out << " " << name;
      }
    }

    bool first=true;
    while(parents.hasNext()) {
      UnitSpec prem=parents.next();
      if (prem.isPropTautology()) {
	continue;
      }
      out << (first ? ' ' : ',');
      out << _is->getUnitIdStr(prem);
      first=false;
    }

    out << "]" << endl;

  }

  virtual bool specialTreatment(UnitSpec cs, Inference::Rule rule)
  {
    if (rule==Inference::SPLITTING && _is->_splittingRecords.find(cs)) {
      handleSplitting(_is->_splittingRecords.get(cs));
      return true;
    }
    return false;
  }

  void handleStep(UnitSpec cs)
  {
    Inference::Rule rule;
    UnitSpecIterator parents=_is->getParents(cs, rule);

    if (specialTreatment(cs, rule)) {
      return;
    }

    while(parents.hasNext()) {
      UnitSpec prem=parents.next();
      ASS(prem!=cs);
      requestProofStep(prem);
    }

    if (!hideProofStep(rule)) {
      printStep(cs);
    }
  }


  /** Clauses that have propositional part assigned are put here
   * to be output as an inference step */
  Stack<UnitSpec> outKernel;
  Set<UnitSpec> handledKernel;

  InferenceStore* _is;
  ostream& out;
  BDD* bdd;

  bool outputAxiomNames;
};

struct InferenceStore::TPTPProofPrinter
: public InferenceStore::ProofPrinter
{
  TPTPProofPrinter(ostream& out, InferenceStore* is)
  : ProofPrinter(out, is) {}

protected:
  //overrides ProofPrinter::specialTreatment
  bool specialTreatment(UnitSpec cs, Inference::Rule rule)
  {
    return false;
  }

  string getRole(Inference::Rule rule, Unit::InputType origin)
  {
    switch(rule) {
    case Inference::INPUT:
      if (origin==Unit::CONJECTURE) {
	return "conjecture";
      }
      else {
	return "axiom";
      }
    case Inference::NEGATED_CONJECTURE:
      return "negated_conjecture";
    default:
      return "plain";
    }
  }

  string tptpRuleName(Inference::Rule rule)
  {
    return StringUtils::replaceChar(Inference::ruleName(rule), ' ', '_');
  }

  string unitIdToTptp(string unitId)
  {
    return "f"+unitId;
  }

  string tptpUnitId(UnitSpec us)
  {
    return unitIdToTptp(_is->getUnitIdStr(us));
  }

  string tptpDefId(UnitSpec us)
  {
    return unitIdToTptp(Int::toString(us.unit()->number())+"_D");
  }

  string bddToString(BDDNode* prop)
  {
    CALL("InferenceStore::TPTPProofPrinter::bddToString");

    return bdd->toTPTPString(prop,bddPrefix);
  }

  string splitsToString(SplitSet* splits)
  {
    CALL("InferenceStore::TPTPProofPrinter::splitsToString");
    ASS_G(splits->size(),0);

    if (splits->size()==1) {
      return splitPrefix+Int::toString(splits->sval());
    }
    SplitSet::Iterator sit(*splits);
    string res("(");
    while(sit.hasNext()) {
      res+=splitPrefix+Int::toString(sit.next());
      if (sit.hasNext()) {
	res+=" | ";
      }
    }
    res+=")";
    return res;
  }

  string quoteAxiomName(string n)
  {
    CALL("InferenceStore::TPTPProofPrinter::quoteAxiomName");

    static string allowedFirst("0123456789abcdefghijklmnopqrstuvwxyz");
    const char* allowed="_ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyz";

    if (n.size()==0 || allowedFirst.find(n[0])==string::npos ||
	n.find_first_not_of(allowed)!=string::npos) {
      n='\''+n+'\'';
    }
    return n;
  }

  string getFofString(string id, string formula, string inference, Inference::Rule rule, Unit::InputType origin=Unit::AXIOM)
  {
    CALL("InferenceStore::TPTPProofPrinter::getFofString");

    return "fof("+id+","+getRole(rule,origin)+",("+"\n"
	+"  "+formula+"),\n"
	+"  "+inference+").";
  }

  string getFormulaString(UnitSpec us)
  {
    CALL("InferenceStore::TPTPProofPrinter::getFormulaString");

    string formulaStr;
    if (us.isClause()) {
      Clause* cl=us.cl();
      formulaStr=getQuantifiedStr(cl);
      if (!bdd->isFalse(us.prop())) {
	formulaStr+=" | "+bddToString(us.prop());
      }
      if (cl->splits() && !cl->splits()->isEmpty()) {
	formulaStr+=" | "+splitsToString(cl->splits());
      }
    }
    else {
      ASS(bdd->isFalse(us.prop()));
      FormulaUnit* fu=static_cast<FormulaUnit*>(us.unit());
      formulaStr=getQuantifiedStr(fu);
    }
    return formulaStr;
  }

  bool hasNewSymbols(Unit* u) {
    CALL("InferenceStore::TPTPProofPrinter::hasNewSymbols");
    bool res = _is->_introducedSymbols.find(u->number());
    ASS(!res || _is->_introducedSymbols.get(u->number()).isNonEmpty());
    return res;
  }
  string getNewSymbols(string origin, string symStr) {
    CALL("InferenceStore::TPTPProofPrinter::getNewSymbols(string,string)");
    return "new_symbols(" + origin + ",[" +symStr + "])";
  }
  /** It is an iterator over SymbolId */
  template<class It>
  string getNewSymbols(string origin, It symIt) {
    CALL("InferenceStore::TPTPProofPrinter::getNewSymbols(string,It)");

    stringstream symsStr;
    while(symIt.hasNext()) {
      SymbolId sym = symIt.next();
      if (sym.first) {
	symsStr << env.signature->functionName(sym.second);
      }
      else {
	symsStr << env.signature->predicateName(sym.second);
      }
      if (symIt.hasNext()) {
	symsStr << ',';
      }
    }
    return getNewSymbols(origin, symsStr.str());
  }
  string getNewSymbols(string origin, Unit* u) {
    CALL("InferenceStore::TPTPProofPrinter::getNewSymbols(string,Unit*)");
    ASS(hasNewSymbols(u));

    SymbolStack& syms = _is->_introducedSymbols.get(u->number());
    return getNewSymbols(origin, SymbolStack::ConstIterator(syms));
  }

  void printStep(UnitSpec us)
  {
    CALL("InferenceStore::TPTPProofPrinter::printStep");

    Inference::Rule rule;
    UnitSpecIterator parents=_is->getParents(us, rule);

    switch(rule) {
    case Inference::SAT_SPLITTING_COMPONENT:
    case Inference::BACKTRACKING_SPLITTING_COMPONENT:
      printBacktrackingSplittingComponentIntroduction(us);
      return;
    case Inference::BACKTRACKING_SPLIT_REFUTATION:
      printBacktrackingSplittingComponentRefutation(us);
      return;
    case Inference::GENERAL_SPLITTING_COMPONENT:
      printGeneralSplittingComponent(us);
      return;
    case Inference::SPLITTING: //only without BDDs
    case Inference::GENERAL_SPLITTING:
      printSplitting(us);
      return;
    case Inference::SPLITTING_COMPONENT:
      printSplittingComponent(us);
      return;
    case Inference::BDDZATION:
      printBddize(us);
      return;
    default: ;
    }


    //get string representing the formula

    string formulaStr=getFormulaString(us);

    //get inference string

    string inferenceStr;
    if (rule==Inference::INPUT) {
      string fileName;
      if (env.options->inputFile()=="") {
	fileName="unknown";
      }
      else {
	fileName="'"+env.options->inputFile()+"'";
      }
      string axiomName;
      if (!outputAxiomNames || !Parse::TPTP::findAxiomName(us.unit(), axiomName)) {
	axiomName="unknown";
      }
      inferenceStr="file("+fileName+","+quoteAxiomName(axiomName)+")";
    }
    else if (!parents.hasNext()) {
      string newSymbolInfo;
      if (us.withoutProp() && hasNewSymbols(us.unit())) {
	newSymbolInfo = getNewSymbols("naming",us.unit());
      }
      inferenceStr="introduced("+tptpRuleName(rule)+",["+newSymbolInfo+"])";
    }
    else {
      ASS(parents.hasNext());
      string statusStr;
      if (rule==Inference::SKOLEMIZE) {
	statusStr="status(esa),"+getNewSymbols("skolem",us.unit());
      }

      inferenceStr="inference("+tptpRuleName(rule);

      inferenceStr+=",["+statusStr+"],[";
      bool first=true;
      while(parents.hasNext()) {
        UnitSpec prem=parents.next();
        if (prem.isPropTautology()) {
          continue;
        }
        if (!first) {
          inferenceStr+=',';
        }
        inferenceStr+=tptpUnitId(prem);
        first=false;
      }
      inferenceStr+="])";
    }

    out<<getFofString(tptpUnitId(us), formulaStr, inferenceStr, rule, us.unit()->inputType())<<endl;
  }

  void printSplittingComponent(UnitSpec us)
  {
    CALL("InferenceStore::TPTPProofPrinter::printSplittingComponent");

    if (_is->_splittingNameLiterals.find(us)) {
      //this one comes from splitting without backtracking without BDDs, which is
      //compatible with the @b printGeneralSplittingComponent function
      printGeneralSplittingComponent(us);
      return;
    }

    ASS(!bdd->isConstant(us.prop())); //the bdd part is the introduced name, so it must be a single variable
    Clause* cl=us.cl();

    string defId=tptpDefId(us);
    out<<getFofString(tptpUnitId(us), getFormulaString(us),
	"inference("+tptpRuleName(Inference::CLAUSIFY)+",[],["+defId+"])", Inference::CLAUSIFY)<<endl;


    unsigned var;
    bool varPos;
    ALWAYS(bdd->parseAtomic(us.prop(), var, varPos));

    string defStr;
    if (cl->length()==1 && (*cl)[0]->arity()==0) {
      defStr=(*cl)[0]->predicateName();
    } else {
      defStr=getQuantifiedStr(cl);
    }
    defStr+=" <=> ";
    if (varPos) {
      defStr+="~";
    }
    string bddSymbolStr = bddPrefix+Int::toString(var);
    defStr+=bddSymbolStr;

    Inference::Rule rule=Inference::SPLITTING_COMPONENT;

    stringstream originStm;
    originStm << "introduced(" << tptpRuleName(rule)
	      << ",[" << getNewSymbols("naming",bddSymbolStr)
	      << "])";

    out<<getFofString(defId, defStr, originStm.str(), rule)<<endl;
  }

  /**
   * This function only prints splitting for splitting without backtracking without
   * BDDs. The SPLITTING inference of splitting without backtracking with BDDs
   * is dealt with in @b printSplittingComponent().
   */
  void printSplitting(UnitSpec us)
  {
    CALL("InferenceStore::TPTPProofPrinter::printSplitting");
//    ASS(bdd->isFalse(us.prop()));
    ASS(us.isClause());

    Inference::Rule rule;
    UnitSpecIterator parents=_is->getParents(us, rule);
    ASS(rule==Inference::GENERAL_SPLITTING || rule==Inference::SPLITTING);


    string inferenceStr="inference("+tptpRuleName(rule)+",[],[";

    //here we rely on the fact that the base premise is always put as the first premise in
    //GeneralSplitting::apply, in SWBSplitterWithoutBDDs::buildAndInsertComponents
    //and in SWBSplitterWithBDDs::buildAndInsertComponents

    ALWAYS(parents.hasNext());
    UnitSpec base=parents.next();
    inferenceStr+=tptpUnitId(base);

    ASS(parents.hasNext()); //we always split off at least one component
    while(parents.hasNext()) {
      UnitSpec comp=parents.next();
      ASS(!bdd->isFalse(comp.prop()) || _is->_splittingNameLiterals.find(comp));
      inferenceStr+=","+tptpDefId(comp);
    }
    inferenceStr+="])";

    out<<getFofString(tptpUnitId(us), getFormulaString(us), inferenceStr, rule)<<endl;
  }

  void printGeneralSplittingComponent(UnitSpec us)
  {
    CALL("InferenceStore::TPTPProofPrinter::printGeneralSplittingComponent");
    ASS(bdd->isFalse(us.prop()));
    ASS(us.isClause());

    Inference::Rule rule;
    UnitSpecIterator parents=_is->getParents(us, rule);
    ASS(!parents.hasNext());

    Literal* nameLit=_is->_splittingNameLiterals.get(us); //the name literal must always be stored

    string defId=tptpDefId(us);

    out<<getFofString(tptpUnitId(us), getFormulaString(us),
	"inference("+tptpRuleName(Inference::CLAUSIFY)+",[],["+defId+"])", Inference::CLAUSIFY)<<endl;


    List<unsigned>* nameVars=0;
    VariableIterator vit(nameLit);
    while(vit.hasNext()) {
      unsigned var=vit.next().var();
      ASS(!nameVars->member(var)); //each variable appears only once in the naming literal
      List<unsigned>::push(var,nameVars);
    }

    string compStr;
    List<unsigned>* compOnlyVars=0;
    Clause::Iterator lits(*us.cl());
    bool first=true;
    bool multiple=false;
    while(lits.hasNext()) {
      Literal* lit=lits.next();
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
        if (!nameVars->member(var) && !compOnlyVars->member(var)) {
          List<unsigned>::push(var,compOnlyVars);
        }
      }
    }
    ASS(!first);

    compStr=getQuantifiedStr(compOnlyVars, compStr, multiple);
    compOnlyVars->destroy();

    string defStr=compStr+" <=> "+Literal::complementaryLiteral(nameLit)->toString();
    defStr=getQuantifiedStr(nameVars, defStr);
    nameVars->destroy();

    SymbolId nameSymbol = SymbolId(false,nameLit->functor());
    stringstream originStm;
    originStm << "introduced(" << tptpRuleName(rule)
	      << ",[" << getNewSymbols("naming",getSingletonIterator(nameSymbol))
	      << "])";

    out<<getFofString(defId, defStr, originStm.str(), rule)<<endl;
  }

  void printBacktrackingSplittingComponentIntroduction(UnitSpec us)
  {
    CALL("InferenceStore::TPTPProofPrinter::printBacktrackingSplittingComponentIntroduction");
    ASS(bdd->isFalse(us.prop()));
    ASS(us.isClause());

    Clause* cl=us.cl();
    ASS(cl->splits());
    ASS_EQ(cl->splits()->size(),1);

    Inference::Rule rule=Inference::BACKTRACKING_SPLITTING_COMPONENT;


    string defId=tptpDefId(us);
    string splitPred = splitsToString(cl->splits());
    string defStr=getQuantifiedStr(cl)+" <=> ~"+splitPred;

    out<<getFofString(tptpUnitId(us), getFormulaString(us),
	"inference("+tptpRuleName(Inference::CLAUSIFY)+",[],["+defId+"])", Inference::CLAUSIFY)<<endl;

    stringstream originStm;
    originStm << "introduced(" << tptpRuleName(rule)
	      << ",[" << getNewSymbols("naming",splitPred)
	      << "])";

    out<<getFofString(defId, defStr, originStm.str(), rule)<<endl;
  }

  void printBacktrackingSplittingComponentRefutation(UnitSpec us)
  {
    CALL("InferenceStore::TPTPProofPrinter::printBacktrackingSplittingComponentRefutation");
    ASS(bdd->isFalse(us.prop()));
    ASS(us.isClause());

    Inference::Rule rule;
    UnitSpecIterator parents=_is->getParents(us, rule);
    ASS_EQ(rule, Inference::BACKTRACKING_SPLIT_REFUTATION);

    //here we rely on the order premises are stored in BSplitter::getAlternativeClauseInference
    ALWAYS(parents.hasNext());
    UnitSpec base=parents.next();
    ALWAYS(parents.hasNext());
    UnitSpec firstComp=parents.next();
    ALWAYS(parents.hasNext());
    UnitSpec refutation=parents.next();
    ASS(!parents.hasNext());
    ASS_EQ(firstComp.cl()->splits()->size(), 1); //the 'definition' clause always has exactly one level in the split history
    ASS_EQ(refutation.cl()->length(), 0); //refutation is always an empty clause

    string inferenceStr="inference("+tptpRuleName(rule)+",[],["+ tptpUnitId(base)+","+
	tptpDefId(firstComp)+","+tptpUnitId(refutation)+"])";

    out<<getFofString(tptpUnitId(us), getFormulaString(us), inferenceStr, rule)<<endl;
  }

  void printBddize(UnitSpec us)
  {
    CALL("InferenceStore::TPTPProofPrinter::printBddize");
    ASS(!bdd->isFalse(us.prop()));
    ASS(us.isClause());

    Inference::Rule rule;
    UnitSpecIterator parents=_is->getParents(us, rule);
    ASS_EQ(rule, Inference::BDDZATION);

    ALWAYS(parents.hasNext());
    UnitSpec parent=parents.next();
    ASS(!parents.hasNext());

    Clause* cl=us.cl();
    IntList* bddVars=_is->_bddizeVars.get(cl);
    ASS(bddVars);


    string premiseIds=tptpUnitId(parent);

    IntList::Iterator vit(bddVars);
    while(vit.hasNext()) {
      int var=vit.next();
      ASS_G(var,0);
      string defId="fbd"+Int::toString(var);
      premiseIds+=","+defId;
      if (!printedBddizeDefs.insert(var)) {
	continue;
      }
      string predName;
      ALWAYS(bdd->getNiceName(var, predName));
      string defStr= predName+" <=> "+bddPrefix+Int::toString(var);
      out<<getFofString(defId, defStr, "introduced("+tptpRuleName(rule)+",[])", rule)<<endl;
    }


    out<<getFofString(tptpUnitId(us), getFormulaString(us),
	"inference("+tptpRuleName(Inference::DEFINITION_FOLDING)+",[],["+premiseIds+"])", Inference::DEFINITION_FOLDING)<<endl;

  }

  void handleSplitting(SplittingRecord* sr)
  {
    CALL("InferenceStore::TPTPProofPrinter::handleSplitting");

    INVALID_OPERATION("The function InferenceStore::TPTPProofPrinter::handleSplitting should not be called");
  }

  DHSet<int> printedBddizeDefs;

  static const char* bddPrefix;
  static const char* splitPrefix;
};

const char* InferenceStore::TPTPProofPrinter::bddPrefix = "$bdd";
const char* InferenceStore::TPTPProofPrinter::splitPrefix = "$spl";

struct InferenceStore::ProofCheckPrinter
: public InferenceStore::ProofPrinter
{
  ProofCheckPrinter(ostream& out, InferenceStore* is)
  : ProofPrinter(out, is) {}

protected:
  string bddToString(BDDNode* node)
  {
    return bdd->toTPTPString(node, "bddPred");
  }

  void printStep(UnitSpec cs)
  {
    Inference::Rule rule;
    UnitSpecIterator parents=_is->getParents(cs, rule);

    out << "fof(r"<<_is->getUnitIdStr(cs)
    	<< ",conjecture, "
    	<< getQuantifiedStr(cs.unit()) <<" | "<<bddToString(cs.prop())
    	<< " ). %"<<Inference::ruleName(rule)<<"\n";

    while(parents.hasNext()) {
      UnitSpec prem=parents.next();
      out << "fof(pr"<<_is->getUnitIdStr(prem)
  	<< ",axiom, "
  	<< getQuantifiedStr(prem.unit());
      if (!bdd->isFalse(prem.prop())) {
	out << " | "<<bddToString(prem.prop());
      }
      out << " ).\n";
    }
    out << "%#\n";
  }

  virtual void printSplitting(SplittingRecord* sr)
  {
    requestProofStep(sr->premise);

    UnitSpec cs=sr->result;
    Clause* cl=cs.cl();

    out << "fof(r"<<_is->getUnitIdStr(cs)
    	<< ",conjecture, "
    	<< getQuantifiedStr(cl) <<" | "<<bddToString(cs.prop())
    	<< " ). %"<<Inference::ruleName(Inference::SPLITTING)<<"\n";

    out << "fof(pr"<<_is->getUnitIdStr(sr->premise)
    	<< ",axiom, "
    	<< getQuantifiedStr(sr->premise.cl()) <<" | "<<bddToString(sr->premise.prop())
    	<< " ).\n";

    Stack<pair<int,Clause*> >::Iterator compIt(sr->namedComps);
    while(compIt.hasNext()) {
      pair<int,Clause*> nrec=compIt.next();

      out << "fof(pr"<<nrec.second->number()<<"_D"
      << ",axiom, ";
      if (nrec.second->length()==1 && (*nrec.second)[0]->arity()==0) {
	out<<(*nrec.second)[0]->predicateName();
      } else {
	out<<getQuantifiedStr(nrec.second);
      }
      out << " <=> ";
      if (nrec.first<0) {
	out << "~";
      }
      out << "bddPred" << abs(nrec.first) << " ).\n";
    }
    out << "%#\n";
  }

  bool hideProofStep(Inference::Rule rule)
  {
    switch(rule) {
    case Inference::INPUT:
    case Inference::CLAUSE_NAMING:
    case Inference::SPLITTING_COMPONENT:
    case Inference::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case Inference::INEQUALITY_SPLITTING:
    case Inference::SKOLEMIZE:
    case Inference::EQUALITY_PROXY_REPLACEMENT:
    case Inference::EQUALITY_PROXY_AXIOM1:
    case Inference::EQUALITY_PROXY_AXIOM2:
    case Inference::BDDZATION:
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
  CALL("InferenceStore::createProofPrinter");

  switch(env.options->proof()) {
  case Options::PROOF_ON:
    return new ProofPrinter(out, this);
  case Options::PROOF_PROOFCHECK:
    return new ProofCheckPrinter(out, this);
  case Options::PROOF_TPTP:
    return new TPTPProofPrinter(out, this);
  case Options::PROOF_OFF:
    return 0;
  }
  ASSERTION_VIOLATION;
  return 0;
}

void InferenceStore::outputProof(ostream& out, Unit* refutation)
{
  CALL("InferenceStore::outputProof(ostream&,Unit*)");

  ScopedPtr<ProofPrinter> pp(createProofPrinter(out));
  if (!pp) {
    return;
  }
  pp->scheduleForPrinting(UnitSpec(refutation));
  pp->print();
}

void InferenceStore::outputProof(ostream& out, UnitList* units)
{
  CALL("InferenceStore::outputProof(ostream&,UnitList*)");

  ScopedPtr<ProofPrinter> pp(createProofPrinter(out));
  if (!pp) {
    return;
  }
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    pp->scheduleForPrinting(UnitSpec(u));
  }
  pp->print();
}

InferenceStore* InferenceStore::instance()
{
  static InferenceStore* inst=0;
  if (!inst) {
    inst = new InferenceStore();
  }
  return inst;
}


}
