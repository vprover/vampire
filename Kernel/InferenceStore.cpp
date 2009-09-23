/**
 * @file InferenceStore.cpp
 * Implements class InferenceStore.
 */

#include "../Lib/Allocator.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/FormulaVarIterator.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Term.hpp"

#include "../Shell/Options.hpp"

#include "InferenceStore.hpp"

namespace Kernel
{

using namespace std;
using namespace Lib;
using namespace Shell;

struct InferenceStore::FullInference
{
  FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) { ASS_L(premCnt, 0xFFFF); }

  void* operator new(size_t,unsigned premCnt)
  {
    size_t size=sizeof(FullInference)+premCnt*sizeof(ClauseSpec);
    size-=sizeof(ClauseSpec);

    return ALLOC_KNOWN(size,"InferenceStore::FullInference");
  }

  size_t occupiedBytes()
  {
    size_t size=sizeof(FullInference)+premCnt*sizeof(ClauseSpec);
    size-=sizeof(ClauseSpec);
    return size;
  }

  int csId;
  unsigned premCnt : 16;
  Inference::Rule rule : 16;
  ClauseSpec premises[1];
};

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
  string res=Int::toString(cs.first->number());
  FullInference* finf;
  if(_data.find(cs,finf)) {
    if(!finf->csId) {
      finf->csId=_nextClIds.insert(cs.first);
    }
    return res+"_"+Int::toString(finf->csId);
  } else {
    //only clause constant prop. part can miss their Kernel-inference.
    if(_bdd->isTrue(cs.second)) {
      return res+"_T";
    } else {
      ASS(_bdd->isFalse(cs.second));
      return res;
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
  _data.insert(getClauseSpec(cl), finf);
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
  _data.insert(getClauseSpec(cl, newProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/4");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=getClauseSpec(cl, oldClProp);
  finf->premises[1]=getClauseSpec(addedCl);
  finf->rule=Inference::COMMON_NONPROP_MERGE;
  _data.insert(getClauseSpec(cl, resultProp), finf);
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
  _data.insert(getClauseSpec(cl, resultProp), finf);
}


void InferenceStore::recordSplitting(Clause* master, BDDNode* oldMasterProp, BDDNode* newMasterProp,
	  unsigned premCnt, Clause** prems, SplittingRecord* srec)
{
  CALL("InferenceStore::recordSplitting");
  ASS(!_bdd->isTrue(newMasterProp));

  FullInference* finf=new (premCnt+1) FullInference(premCnt+1);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }
  finf->premises[premCnt]=getClauseSpec(master, oldMasterProp);

  finf->rule=Inference::SPLITTING;
  ClauseSpec mcs=getClauseSpec(master, newMasterProp);
  _data.insert(mcs, finf);

  _splittingRecords.insert(mcs, srec);
}

string getQuantifiedStr(Unit* u)
{
  Set<unsigned> vars;
  string res;
  if(u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
	Term::VariableIterator vit( (*cl)[i] );
	while(vit.hasNext()) {
	  vars.insert(vit.next().var());
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
    dummyTautIntroduction.rule=Inference::TAUTOLOGY_INTRODUCTION;

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
    out << " ("<<cl->age()<<':'<<cl->weight()<<") ";

    out <<"["<<Inference::ruleName(finf->rule);
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
      out << cl->nonPropToString() << " ("<<cl->age()<<':'<<cl->weight()<<")";
    } else {
      FormulaUnit* fu=static_cast<FormulaUnit*>(unit);
      out << fu->formula()->toString();
    }
    out << " [" << unit->inference()->name();
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

    ClauseSpec prevCs=getClauseSpec(cl, sr->oldResBDD);
    out <<"["<<Inference::ruleName(Inference::SPLITTING)<<" "
      <<is->getClauseIdStr(sr->premise)<<","
      <<is->getClauseIdStr(prevCs);

    requestKernelProofStep(prevCs);

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
      out<<" <=> bddPred"<<nrec.first
	  <<" ["<<Inference::ruleName(Inference::SPLITTING_COMPONENT)<<"]\n";
    }
  }

  virtual bool hideProofStep(Inference::Rule rule)
  {
    return false;
  }

  void requestKernelProofStep(ClauseSpec prem)
  {
    if(!handledKernel.contains(prem)) {
      handledKernel.insert(prem);
      outKernel.push(prem);
    }
  }

  void print()
  {
    while(outKernel.isNonEmpty()) {
      ClauseSpec cs=outKernel.pop();
      FullInference* finf;
      if(bdd->isTrue(cs.second)) {
	//a tautology does not need any proof
	ASS(!is->_data.find(cs));
	if(!hideProofStep(Inference::TAUTOLOGY_INTRODUCTION)) {
	  printProofStepHead(cs, &dummyTautIntroduction);
	  printProofStepTail();
	}
      } else if(is->_data.find(cs, finf)) {
	bool hideStep=hideProofStep(finf->rule);

	if(finf->rule==Inference::SPLITTING && is->_splittingRecords.find(cs)) {
	  printSplitting(is->_splittingRecords.get(cs));
	  continue;
	}

	if(!hideStep) {
	  printProofStepHead(cs, finf);
	}

	for(unsigned i=0;i<finf->premCnt;i++) {
	  ClauseSpec prem=finf->premises[i];
	  ASS(prem!=cs);
	  Clause* premCl=prem.first;
	  if(!hideStep) {
	    printProofStepPremise(prem, i==0);
	  }
	  ASS(premCl->prop());
	  requestKernelProofStep(prem);
	}
	if(!hideStep) {
	  printProofStepTail();
	}
      } else {
	Clause* cl=cs.first;
	Inference* inf = cl->inference();
	bool hideStep=hideProofStep(inf->rule());

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
    ClauseSpec prevCs=getClauseSpec(cl, sr->oldResBDD);

    requestKernelProofStep(prevCs);

    out << "fof(r"<<is->getClauseIdStr(cs)
    	<< ",conjecture, "
    	<< getQuantifiedStr(cl) <<" | "<<bddToString(cs.second)
    	<< " ). %"<<Inference::ruleName(Inference::SPLITTING)<<"\n";

    out << "fof(pr"<<is->getClauseIdStr(sr->premise)
    	<< ",axiom, "
    	<< getQuantifiedStr(sr->premise.first) <<" | "<<bddToString(sr->premise.second)
    	<< " ).\n";

    out << "fof(pr"<<is->getClauseIdStr(prevCs)
    	<< ",axiom, "
    	<< getQuantifiedStr(prevCs.first) <<" | "<<bddToString(prevCs.second)
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
      out<<" <=> bddPred"<<nrec.first
      	<< " ).\n";
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
