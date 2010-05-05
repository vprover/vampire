/**
 * @file InferenceStore.cpp
 * Implements class InferenceStore.
 */

#include "../Lib/Allocator.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/SharedSet.hpp"
#include "../Lib/Stack.hpp"

#include "../Shell/LaTeX.hpp"
#include "../Shell/Options.hpp"
#include "../Shell/Parser.hpp"

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
    premises[i].first->incRefCnt();
  }
}



InferenceStore::InferenceStore()
: _bdd(BDD::instance())
{
}


InferenceStore::ClauseSpec InferenceStore::getClauseSpec(Clause* cl)
{
  return ClauseSpec(cl, cl->prop());
}
InferenceStore::ClauseSpec InferenceStore::getClauseSpec(Clause* cl, BDDNode* prop)
{
  return ClauseSpec(cl, prop);
}

string InferenceStore::getClauseIdStr(ClauseSpec cs)
{
  string suffix=getClauseIdSuffix(cs);
  if(suffix=="") {
    return Int::toString(cs.first->number());
  }
  return Int::toString(cs.first->number())+"_"+suffix;
}

string InferenceStore::getClauseIdSuffix(ClauseSpec cs)
{
  FullInference* finf;
  if(_data.find(cs,finf)) {
    if(!finf->csId) {
      finf->csId=_nextClIds.insert(cs.first);
    }
    return Int::toString(finf->csId);
  } else {
    //only clause constant prop. part can miss their Kernel-inference.
    if(_bdd->isTrue(cs.second)) {
      return "T";
    } else {
      ASS(_bdd->isFalse(cs.second));
      return "";
    }
  }
}

void InferenceStore::recordNonPropInference(Clause* cl)
{
  CALL("InferenceStore::recordNonPropInference/1");

  bool nonTrivialProp=!_bdd->isConstant(cl->prop());
  if(!nonTrivialProp) {
    Inference* cinf=cl->inference();
    Inference::Iterator it = cinf->iterator();
    while (cinf->hasNext(it)) {
      Clause* prem=static_cast<Clause*>(cinf->next(it));
      ASS(prem->isClause());
      if(!_bdd->isFalse(prem->prop())) {
        nonTrivialProp=true;
        break;
      }
    }
  }

  if(nonTrivialProp) {
    recordNonPropInference(cl, cl->inference());
  }


}

void InferenceStore::recordNonPropInference(Clause* cl, Inference* cinf)
{
  CALL("InferenceStore::recordNonPropInference/2");
  ASS(!_bdd->isTrue(cl->prop()));

  static Stack<Clause*> prems(8);
  prems.reset();

  Inference::Iterator it = cinf->iterator();
  while (cinf->hasNext(it)) {
    Clause* prem=static_cast<Clause*>(cinf->next(it));
    ASS(prem->isClause());
    prems.push(prem);
  }

  unsigned premCnt=prems.size();
  FullInference* finf=new (premCnt) FullInference(premCnt);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }
  finf->rule=cinf->rule();
  finf->increasePremiseRefCounters();
  _data.set(getClauseSpec(cl), finf);
}

void InferenceStore::recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp)
{
  CALL("InferenceStore::recordPropReduce");

  if(_bdd->isTrue(cl->prop())) {
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
  finf->premises[0]=getClauseSpec(cl, oldProp);
  finf->rule=rule;
  finf->increasePremiseRefCounters();

  _data.set(getClauseSpec(cl, newProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/4");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=getClauseSpec(cl, oldClProp);
  finf->premises[1]=getClauseSpec(addedCl);
  finf->rule=Inference::COMMON_NONPROP_MERGE;
  finf->increasePremiseRefCounters();

  _data.set(getClauseSpec(cl, resultProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldProp, BDDNode* addedProp, BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/4");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=getClauseSpec(cl, oldProp);
  finf->premises[1]=getClauseSpec(cl, addedProp);
  finf->rule=Inference::COMMON_NONPROP_MERGE;
  finf->increasePremiseRefCounters();

  _data.set(getClauseSpec(cl, resultProp), finf);
}


void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, ClauseSpec* addedCls, int addedClsCnt,
	BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/5");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (addedClsCnt+1) FullInference(addedClsCnt+1);
  for(int i=0;i<addedClsCnt;i++) {
    finf->premises[i]=addedCls[i];
  }
  finf->premises[addedClsCnt]=getClauseSpec(cl, oldClProp);
  finf->rule=Inference::COMMON_NONPROP_MERGE;
  finf->increasePremiseRefCounters();

  _data.set(getClauseSpec(cl, resultProp), finf);
}


void InferenceStore::recordSplitting(SplittingRecord* srec, unsigned premCnt, Clause** prems)
{
  CALL("InferenceStore::recordSplitting");
  ASS(!_bdd->isTrue(srec->result.second));

  FullInference* finf=new (premCnt) FullInference(premCnt);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }

  finf->rule=Inference::SPLITTING;
  finf->increasePremiseRefCounters();

  _data.set(srec->result, finf);

  //There is no need to increase reference counters in splitting premises,
  //as they're stored in the variant index of Splitter object, so won't get
  //deleted.
  _splittingRecords.set(srec->result, srec);
}

/**
 * Called before a clause is destroyed
 *
 * Deletes all records for the clause @b cl that can be efficiently reached,
 * as the clause is being destroyed and there will be no further need of them.
 */
void InferenceStore::deleteClauseRecords(Clause* cl)
{
  if(!cl->prop()) {
    return;
  }
  ClauseSpec cs=getClauseSpec(cl);
  if(_data.find(cs)) {
    _data.remove(cs);
  }
}

VirtualIterator<InferenceStore::ClauseSpec> InferenceStore::getParents(Clause* cl)
{
  ClauseSpec cs=getClauseSpec(cl);

  FullInference* finf;
  if(!_data.find(cs, finf)) {
    //TODO: implement retrieval of parents from inferences not stored in _data
    return VirtualIterator<InferenceStore::ClauseSpec>::getEmpty();
  }

  return pvi( PointerIterator<ClauseSpec>(finf->premises, finf->premises+finf->premCnt) );
}

struct Cs2UsFn
{
  DECL_RETURN_TYPE(InferenceStore::UnitSpec);
  InferenceStore::UnitSpec operator()(InferenceStore::ClauseSpec cs)
  {
    return InferenceStore::UnitSpec(cs.first, cs.second);
  }
};

VirtualIterator<InferenceStore::UnitSpec> InferenceStore::getUnitParents(Unit* u, BDDNode* prop)
{
  CALL("InferenceStore::getUnitParents");

  if(prop && _bdd->isTrue(prop)) {
    return VirtualIterator<InferenceStore::UnitSpec>::getEmpty();
  }
  if(u->isClause() && prop) {
    Clause* cl=static_cast<Clause*>(u);
    FullInference* finf;
    if(_data.find(ClauseSpec(cl,prop), finf)) {
      return pvi( getMappingIterator(
        PointerIterator<ClauseSpec>(finf->premises, finf->premises+finf->premCnt),
        Cs2UsFn()
      ) );
    }
  }
  List<UnitSpec>* res=0;
  Inference::Iterator iit=u->inference()->iterator();
  while(u->inference()->hasNext(iit)) {
    Unit* premUnit=u->inference()->next(iit);
    List<UnitSpec>::push(UnitSpec(premUnit), res);
  }
  return pvi( List<UnitSpec>::DestructiveIterator(res) );
}


string getQuantifiedStr(Unit* u)
{
  Set<unsigned> vars;
  string res;
  if(u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      TermVarIterator vit( (*cl)[i] );
      while(vit.hasNext()) {
	vars.insert(vit.next());
      }
    }
    res=cl->nonPropToString();
  } else {
    Formula* formula=static_cast<FormulaUnit*>(u)->formula();
    FormulaVarIterator fvit( formula );
    while(fvit.hasNext()) {
	vars.insert(fvit.next());
    }
    res=formula->toString();
  }
  if(!vars.numberOfElements()) {
    return res;
  }
  Set<unsigned>::Iterator vit(vars);
  string varStr;
  bool first=true;
  while(vit.hasNext()) {
    if(!first) {
	varStr+=",";
    }
    varStr+=string("X")+Int::toString(vit.next());
    first=false;
  }

  return "( ! ["+varStr+"] : ("+res+") )";
}

struct InferenceStore::ProofPrinter
{
  ProofPrinter(Unit* refutation, ostream& out, InferenceStore* is)
  : is(is), out(out), bdd(BDD::instance()), dummyTautIntroduction(0)
  {
    CALL("InferenceStore::ProofPrinter::ProofPrinter");

    dummyTautIntroduction.rule=Inference::TAUTOLOGY_INTRODUCTION;

    outputAxiomNames=env.options->outputAxiomNames();

    if( refutation->isClause() && static_cast<Clause*>(refutation)->prop() ) {
      Clause* refCl=static_cast<Clause*>(refutation);
      ASS( bdd->isFalse(refCl->prop()) );
      ClauseSpec cs=getClauseSpec(refCl);
      outKernel.push(cs);
      handledKernel.insert(cs);
    } else {
      outShell.push(refutation);
      handledShell.insert(refutation);
    }
  }

  virtual ~ProofPrinter() {}

  virtual void printProofStepHead(ClauseSpec cs, FullInference* finf)
  {
    Clause* cl=cs.first;

    out << is->getClauseIdStr(cs) << ". "
	<< cl->nonPropToString();
    if(!bdd->isFalse(cs.second)) {
	out << " | "<<bdd->toString(cs.second);
    }
    if(cl->splits() && !cl->splits()->isEmpty()) {
      out << " {" << cl->splits()->toString() << "}";
    }
    out << " ("<<cl->age()<<':'<<cl->weight()<<") ";

    out <<"["<<Inference::ruleName(finf->rule);
    if(outputAxiomNames && finf->rule==Inference::INPUT) {
      string name;
      if(Parser::findAxiomName(cl, name)) {
	out << " " << name;
      }
    }
  }

  virtual void printProofStepPremise(ClauseSpec cs, bool first)
  {
    out << (first ? ' ' : ',');
    out << is->getClauseIdStr(cs);
  }

  virtual void printProofStepHead(Unit* unit)
  {
    out << unit->number() << ". ";
    if(unit->isClause()) {
      Clause* cl=static_cast<Clause*>(unit);
      out << cl->nonPropToString();
      if(cl->splits() && !cl->splits()->isEmpty()) {
        out << " {" << cl->splits()->toString() << "}";
      }
      out << " ("<<cl->age()<<':'<<cl->weight()<<")";
    } else {
      FormulaUnit* fu=static_cast<FormulaUnit*>(unit);
      out << fu->formula()->toString();
    }
    out << " [" << unit->inference()->name();
    if(outputAxiomNames && unit->inference()->rule()==Inference::INPUT) {
      string name;
      if(Parser::findAxiomName(unit, name)) {
	out << " " << name;
      }
    }
  }

  virtual void printProofStepPremise(Unit* unit, bool first)
  {
    out << (first ? ' ' : ',');
    out << unit->number();
  }

  virtual void printProofStepTail()
  {
    out << "]\n";
  }

  virtual void printSplitting(SplittingRecord* sr)
  {
    requestKernelProofStep(sr->premise);

    ClauseSpec cs=sr->result;
    Clause* cl=cs.first;
    out << is->getClauseIdStr(cs) << ". "
	<< cl->nonPropToString();
    if(!bdd->isFalse(cs.second)) {
      out <<" | "<<bdd->toString(cs.second);
    }
    out << " ("<<cl->age()<<':'<<cl->weight()<<") ";

    out <<"["<<Inference::ruleName(Inference::SPLITTING)<<" "
      <<is->getClauseIdStr(sr->premise);

    Stack<pair<int,Clause*> >::Iterator compIt(sr->namedComps);
    while(compIt.hasNext()) {
      out<<","<<compIt.next().second->number()<<"_D";
    }
    out <<"]\n";

    Stack<pair<int,Clause*> >::Iterator compIt2(sr->namedComps);
    while(compIt2.hasNext()) {
      pair<int,Clause*> nrec=compIt2.next();
      out<<nrec.second->number()<<"_D. ";
      if(nrec.second->length()==1 && (*nrec.second)[0]->arity()==0) {
	out<<(*nrec.second)[0]->predicateName();
      } else {
	out<<getQuantifiedStr(nrec.second);
      }
      out<<" <=> ";
      if(nrec.first>0) {
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

  void requestKernelProofStep(ClauseSpec prem)
  {
    if(!bdd->isTrue(prem.second) && !handledKernel.contains(prem)) {
      handledKernel.insert(prem);
      outKernel.push(prem);
    }
  }

  void print()
  {
    CALL("InferenceStore::ProofPrinter::print");

    while(outKernel.isNonEmpty()) {
      ClauseSpec cs=outKernel.pop();
      FullInference* finf;
      if(bdd->isTrue(cs.second)) {
	//tautologies should not be printed out
	ASSERTION_VIOLATION;
      } else if(is->_data.find(cs, finf)) {
	bool hideStep=hideProofStep(finf->rule);

	if(finf->rule==Inference::SPLITTING && is->_splittingRecords.find(cs)) {
	  bdd->allowDefinitionOutput(false);
	  printSplitting(is->_splittingRecords.get(cs));
	  bdd->allowDefinitionOutput(true);
	  continue;
	}

	bdd->allowDefinitionOutput(false);
	if(!hideStep) {
	  printProofStepHead(cs, finf);
	}

	for(unsigned i=0;i<finf->premCnt;i++) {
	  ClauseSpec prem=finf->premises[i];
	  ASS(prem!=cs);
	  Clause* premCl=prem.first;
	  if(!hideStep && !bdd->isTrue(prem.second)) {
	    printProofStepPremise(prem, i==0);
	  }
	  ASS(premCl->prop());
	  requestKernelProofStep(prem);
	}
	if(!hideStep) {
	  printProofStepTail();
	}

	bdd->allowDefinitionOutput(true);
      } else {
	Clause* cl=cs.first;
	Inference* inf = cl->inference();
	bool hideStep=hideProofStep(inf->rule());

	bdd->allowDefinitionOutput(false);

	if(!hideStep) {
	  printProofStepHead(cl);
	}
	Inference::Iterator it = inf->iterator();
	bool first=true;
	while (inf->hasNext(it)) {
	  Unit* prem=inf->next(it);
	  if(!hideStep) {
	    printProofStepPremise(prem, first);
	  }
	  first=false;
	  if(prem->isClause() && static_cast<Clause*>(prem)->prop()) {
	    //this branch is for clauses that were inserted as input into the SaturationAlgorithm object
	    ClauseSpec premCS=getClauseSpec(static_cast<Clause*>(prem), bdd->getFalse());
	    requestKernelProofStep(premCS);
	  } else {
	    if(!handledShell.contains(prem)) {
	      handledShell.insert(prem);
	      outShell.push(prem);
	    }
	  }
	}
	if(!hideStep) {
	  printProofStepTail();
	}
	bdd->allowDefinitionOutput(true);

      }
    }

    while(outShell.isNonEmpty()) {
      Unit* unit=outShell.pop();
      Inference* inf = unit->inference();
      bool hideStep=hideProofStep(inf->rule());

      if(!hideStep) {
	printProofStepHead(unit);
      }
      Inference::Iterator it = inf->iterator();
      bool first=true;
      while (inf->hasNext(it)) {
	Unit* prem=inf->next(it);
	if(!hideStep) {
	  printProofStepPremise(prem, first);
	}
	first=false;
	if(!handledShell.contains(prem)) {
	  handledShell.insert(prem);
	  outShell.push(prem);
	}
      }
      if(!hideStep) {
	printProofStepTail();
      }
    }
  }

  /** Clauses that have propositional part assigned are put here
   * to be output as an inference step */
  Stack<ClauseSpec> outKernel;
  Set<ClauseSpec> handledKernel;

  Stack<Unit*> outShell;
  Set<Unit*> handledShell;

  InferenceStore* is;
  ostream& out;
  BDD* bdd;

  FullInference dummyTautIntroduction;

  bool outputAxiomNames;
};

struct InferenceStore::TPTPProofCheckPrinter
: InferenceStore::ProofPrinter
{
  TPTPProofCheckPrinter(Unit* refutation, ostream& out, InferenceStore* is)
  : ProofPrinter(refutation, out, is) {}

  string bddToString(BDDNode* node)
  {
    return bdd->toTPTPString(node, "bddPred");
  }

  void printProofStepHead(ClauseSpec cs, FullInference* finf)
  {
    Clause* cl=cs.first;
    out << "fof(r"<<is->getClauseIdStr(cs)
    	<< ",conjecture, "
    	<< getQuantifiedStr(cl) <<" | "<<bddToString(cs.second)
    	<< " ). %"<<Inference::ruleName(finf->rule)<<"\n";
  }

  void printProofStepPremise(ClauseSpec cs, bool first)
  {
    Clause* cl=cs.first;
    out << "fof(pr"<<is->getClauseIdStr(cs)
	<< ",axiom, "
	<< getQuantifiedStr(cl)<<" | "<<bddToString(cs.second)
    	<< " ).\n";
  }

  void printProofStepHead(Unit* unit)
  {
    out << "fof(r"<<unit->number()<<",conjecture, "
    	<< getQuantifiedStr(unit)<<" ). %"<<unit->inference()->name()<<"\n";
  }

  void printProofStepPremise(Unit* unit, bool first)
  {
    out << "fof(pr"<<unit->number()<<",axiom, "
    	<< getQuantifiedStr(unit)<<" ).\n";
  }

  void printProofStepTail()
  {
    out << "%#\n";
  }

  virtual void printSplitting(SplittingRecord* sr)
  {
    requestKernelProofStep(sr->premise);

    ClauseSpec cs=sr->result;
    Clause* cl=cs.first;

    out << "fof(r"<<is->getClauseIdStr(cs)
    	<< ",conjecture, "
    	<< getQuantifiedStr(cl) <<" | "<<bddToString(cs.second)
    	<< " ). %"<<Inference::ruleName(Inference::SPLITTING)<<"\n";

    out << "fof(pr"<<is->getClauseIdStr(sr->premise)
    	<< ",axiom, "
    	<< getQuantifiedStr(sr->premise.first) <<" | "<<bddToString(sr->premise.second)
    	<< " ).\n";

    Stack<pair<int,Clause*> >::Iterator compIt(sr->namedComps);
    while(compIt.hasNext()) {
      pair<int,Clause*> nrec=compIt.next();

      out << "fof(pr"<<nrec.second->number()<<"_D"
      << ",axiom, ";
      if(nrec.second->length()==1 && (*nrec.second)[0]->arity()==0) {
	out<<(*nrec.second)[0]->predicateName();
      } else {
	out<<getQuantifiedStr(nrec.second);
      }
      out << " <=> ";
      if(nrec.first<0) {
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
    case Inference::NEGATED_CONJECTURE:
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
};


void InferenceStore::outputProof(ostream& out, Unit* refutation)
{
  CALL("InferenceStore::outputProof");

  switch(env.options->proof()) {
  case Options::PROOF_ON:
  {
    ProofPrinter pp(refutation, out, this);
    pp.print();
    return;
  }
  case Options::PROOF_SUCCINCT:
  {
    TPTPProofCheckPrinter pp(refutation, out, this);
    out << "%#\n";
    pp.print();
    return;
  }
  case Options::PROOF_OFF:
    return;
  }
}


InferenceStore* InferenceStore::instance()
{
  static InferenceStore* inst=0;
  if(!inst) {
    inst=new InferenceStore();
  }
  return inst;
}


}
