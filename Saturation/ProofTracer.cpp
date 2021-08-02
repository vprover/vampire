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
 * @file Saturation/ProofTracer.cpp
 * Implements class ProofTracer.
 */

#include "ProofTracer.hpp"

#include "Lib/ScopedLet.hpp"
#include "Lib/VString.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Parse/TPTP.hpp"

#include <unordered_map>
#include <fstream>

using namespace Saturation;
using namespace std;

void ProofTracer::onNewClause(Clause* cl)
{
  Clause* match = _tp->findVariant(cl);
  if (match != 0) {
    TracedClauseInfo* info = _tp->getClauseInfo(match);
    cout << "New " << cl->toString() << endl;
    cout << "ma " << info->_name << " IK: " << info->_ik << " " << info->_inf << " CL: " << match->toNiceString() << endl;

    if (_tp->_expecting.find(match)) {
      _tp->_expecting.remove(match);
      // cout << "Was expected! Still expecting "; _tp->listExpecteds();
    }

    if (info->_stalkees.size()) {
      // cout << "Already stalking" << endl;
    } else {
      // at the moment of assigning a (first) stalkee, we decrease the counter of children to find the expected ones...
      for (unsigned i = 0; i < info->_children.size(); i++) {
        Clause* ch = info->_children[i];
        TracedClauseInfo* ch_info = _tp->getClauseInfo(ch);
        ch_info->_numAwokenParents++;
        if (ch_info->_numAwokenParents == ch_info->_parents.size()) {
          // cout << "Newly expecting " << ch_info->_name << " in addition to "; _tp->listExpecteds();
          _tp->_expecting.insert(ch);
        }
      }
    }

    // in any case, add this guy to the stalkees
    info->_stalkees.push(cl);

    for (unsigned j = 0; j < info->_stalkees.size(); j++) {
      cout << "  s: ";
      printWithStore(info->_stalkees[j]);
    }

    for (unsigned i = 0; i < info->_parents.size(); i++) {
      Clause* par = info->_parents[i];
      TracedClauseInfo* p_info = _tp->getClauseInfo(par);
      cout << "  p: " << p_info->_name << endl;
      for (unsigned j = 0; j < p_info->_stalkees.size(); j++) {
        cout << "    s: ";
        printWithStore(p_info->_stalkees[j]);
      }
    }
    cout << endl;

    /*
    cout << "Currently expecting:" << endl;
    _tp->listExpectedsDetails();
    */

    cout << endl;
  }
}


void ProofTracer::onInputClause(Clause* cl)
{
  ASS(cl->isTraced());

  //cout << "Init " << cl->toString() << endl;

  Clause* match = _tp->findVariant(cl);
  if (match != 0) {
    TracedClauseInfo* info = _tp->getClauseInfo(match);

    /*
    cout << "Init " << cl->toString() << endl;
    cout << " matched " << info->_name << endl;
    */
    _tp->initalBorn();

    /*
    for (unsigned i = 0; i < info->_children.size(); i++) {
      Clause* ch = info->_children[i];
      TracedClauseInfo* ch_info = _tp->getClauseInfo(ch);
      cout << " would notify child " << ch_info->_name << endl;
      cout << " ik: " << ch_info->_ik << endl;
      cout << " pc: " << ch_info->_parents.size() << endl;
    }
    */
  }
}

void ProofTracer::onInputFinished()
{
  cout << "Input finished" << endl;

  _tp->onInputFinished();
}


void ProofTracer::onActivation(Clause* cl)
{
  ASS(cl->isTraced());

  _tp->_lastActivationMatch = _tp->findVariant(cl);
  if (_tp->_lastActivationMatch != 0) {
    TracedClauseInfo* info = _tp->getClauseInfo(_tp->_lastActivationMatch);

    cout << "Activate " << cl->toString() << endl;
    cout << " matched " << info->_name << endl;
  }
}

void ProofTracer::onActivationFinished(Clause* cl)
{
  if (_tp->_lastActivationMatch) {
    ASS_EQ(_tp->_lastActivationMatch,_tp->findVariant(cl));

    TracedClauseInfo* info = _tp->getClauseInfo(_tp->_lastActivationMatch);
  }
}


void ProofTracer::TracedProof::init()
{
  DHMap<Clause*, TracedClauseInfo*>::Iterator it(_clInfo);
  while (it.hasNext()) {
    Clause* cl;
    TracedClauseInfo* info;
    it.next(cl,info);

    ASS_EQ((cl == _theEmpty),info->isTerminal()); // exactly the Empty is Terminal

    if (info->isInital()) {
      _unbornInitials++;
    }
  }

  cout << "TracedProof initilized!" << endl;
  cout << "proof size: " << _clInfo.size() << endl << endl;
  // cout << "_unbornInitials: " << _unbornInitials << endl;
}

void ProofTracer::TracedProof::onInputFinished()
{
  if (_unbornInitials > 0) {
    cout << "_unbornInitials: " << _unbornInitials << endl;
    DHMap<Clause*, TracedClauseInfo*>::Iterator it(_clInfo);
    while (it.hasNext()) {
      Clause* cl;
      TracedClauseInfo* info;
      it.next(cl,info);

      if (info->isInital() && info->_stalkees.size() == 0) {
        cout << info->_name << " " << cl->toString() << endl;
      }
    }
  } else {
    cout << "All initials recognized!" << endl << endl;
  }
}

void ProofTracer::TracedProof::listExpecteds()
{
  // just print all on one line
  DHSet<Clause*>::Iterator it(_expecting);
  if (!it.hasNext()) {
    cout << "NONE";
  } else {
    while(it.hasNext()) {
      TracedClauseInfo* info = _clInfo.get(it.next());
      cout << " " << info->_name;
    }
  }
  cout << endl;
}

void ProofTracer::TracedProof::listExpectedsDetails()
{
  // list each expected's parents' stalkee's store! ;)

  DHSet<Clause*>::Iterator it(_expecting);
  while(it.hasNext()) {
    Clause* e = it.next();
    TracedClauseInfo* e_info = _clInfo.get(e);
    cout << "  E: " << e_info->_name << " IK: " << e_info->_ik << " " << e_info->_inf << " CL: " << e->toNiceString() << endl;
    for (unsigned i = 0; i < e_info->_parents.size(); i++) {
      TracedClauseInfo* p_info = _clInfo.get(e_info->_parents[i]);
      cout << "    p: " << p_info->_name << endl;
      for (unsigned j = 0; j < p_info->_stalkees.size(); j++) {
        cout << "      s: ";
        printWithStore(p_info->_stalkees[j]);
      }
    }
  }
}

void ProofTracer::TracedProof::finalInfo()
{
  cout << "finalInfo" << endl;

  ClauseList::Iterator it(_inOrder);
  while(it.hasNext()) {
    Clause* cl = it.next();

    // cout << "cl " << cl->toString() << endl;

    TracedClauseInfo* info = _clInfo.get(cl);

    cout << info->_name << " IK: " << info->_ik << " " << info->_inf << " CL: " << cl->toNiceString() << endl;
    cout << "  parents:";
    if (info->_parents.size() == 0) {
      cout << " NONE";
    } else {
      for (unsigned i = 0; i < info->_parents.size(); i++) {
        TracedClauseInfo* p_info = _clInfo.get(info->_parents[i]);
        cout << " " << p_info->_name;
      }
    }
    cout << endl;

    cout << "  children:";
    if (info->_children.size() == 0) {
      cout << " NONE";
    } else {
      for (unsigned i = 0; i < info->_children.size(); i++) {
        TracedClauseInfo* c_info = _clInfo.get(info->_children[i]);
        cout << " " << c_info->_name;
      }
    }
    cout << endl;

    for (unsigned i = 0; i < info->_stalkees.size(); i++) {
      cout << "  s: ";
      printWithStore(info->_stalkees[i]);
    }

    cout << endl;
  }
}

/***************************************************************************************
 * Parsing and initialization below:
 */

ProofTracer::ParsedProof* ProofTracer::getParsedProof(const vstring& proofFileName)
{
  ParsedProof* resultProof = new ParsedProof();

  istream* input;
  {
    input=new ifstream(proofFileName.c_str());
    if (input->fail()) {
      USER_ERROR("Cannot open problem file: "+proofFileName);
    }
  }

  Parse::TPTP parser(*input);

  parser.setUnitSourceMap(&resultProof->sources);

  // make the parser store axiomsNames for us here (for now)
  ScopedLet<DHMap<unsigned, vstring>*> axiomNamesSwap(Parse::TPTP::_axiomNames,&resultProof->names);

  try{
    parser.parse();
  }
  catch (UserErrorException& exception) {
    vstring msg = exception.msg();
    throw Parse::TPTP::ParseErrorException(msg,parser.lineNumber());
  }

  resultProof->units = parser.units();

  return resultProof;
}

Clause* ProofTracer::unitToClause(Unit* u)
{
  Formula* f = static_cast<FormulaUnit*>(u)->formula();

  // cout << f->toString() << endl;

  if (f->connective() == FALSE) {
    return new(0) Clause(0,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
  }

  if (f->connective() == FORALL) {
    // ignore one forall and jump directly to the disjunction
    f = f->qarg();
  }

  Clause* res;

  // the singleton case
  if (f->connective() == LITERAL) {
    res = new(1) Clause(1,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
    (*res)[0] = f->literal();
    return res;
  }

  ASS_EQ(f->connective(),OR);
  FormulaList* args = f->args();
  unsigned len = FormulaList::length(args);
  res = new(len) Clause(len,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
  unsigned idx = 0;
  for (;args != nullptr; args = args->tail()) {
    Formula* arg = args->head();
    ASS_EQ(arg->connective(),LITERAL);
    (*res)[idx++] = arg->literal();
  }

  return res;
}

// inferences that work on clauses;
static const DHMap<vstring, ProofTracer::InferenceKind> inference_info = {
    {"subsumption_resolution", ProofTracer::SIMPLIFYING},
    {"cnf_transformation", ProofTracer::ICP},
    {"trivial_inequality_removal", ProofTracer::TRIVSIMP},
    {"superposition", ProofTracer::GENERATING},
    {"forward_demodulation", ProofTracer::SIMPLIFYING},
    {"backward_demodulation", ProofTracer::SIMPLIFYING},
    {"resolution", ProofTracer::GENERATING},
    {"definition_unfolding", ProofTracer::ICP},
};

ProofTracer::TracedProof* ProofTracer::prepareTracedProof(ProofTracer::ParsedProof* pp)
{
  DHMap<vstring,Clause*> clausesByNames;
  // a temp structure to be filled up during the first pass of the following loop and used after (when clauses have names)
  DHMap<vstring,Stack<vstring>> rememberedPremises;

  TracedProof *tp = new TracedProof;

  // we assume the units in pp->units come in topological order

  // names that should be processed
  DHSet<vstring> todo;

  ASS(pp->units); // have at least the empty clause in the proof
  FormulaUnit* theEmpty = static_cast<FormulaUnit*>(pp->units->head());
  ASS(theEmpty->formula()->connective() == FALSE); // the empty clause
  todo.insert(pp->names.get(theEmpty->number()));

  for (UnitList* units = pp->units; units != 0;units = units->tail()) {
    Unit* u = units->head();
    vstring uname;

    // cout << "Proof unit: " << u->toString() << endl;

    if (pp->names.find(u->number())) {
      uname = pp->names.get(u->number());
    } else { // the TPTP parser was very agile and negated a conjecture formula (and the proof printer had also been very agile and printed it with the conjecture role into the proof)
      Inference& i = u->inference();
      ASS_EQ(i.rule(),InferenceRule::NEGATED_CONJECTURE);
      Inference::Iterator it = i.iterator();
      ASS(i.hasNext(it));
      u = i.next(it);
      ASS(!i.hasNext(it));
      units->setHead(u);

      // we took the original (unnegated) formula instead
      // cout << "Corrected to: " << u->toString() << endl;
      uname = pp->names.get(u->number());
    }
    // cout << "Named: " << uname << endl;

    if (!todo.contains(uname)) {
      continue;
    }

    InferenceKind ik = ICP;
    vstring inf = "input";
    Stack<vstring> premises; // empty by default

    Parse::TPTP::SourceRecord* rec = pp->sources.get(u);
    if (rec->isFile()) {
      // Parse::TPTP::FileSourceRecord* frec = static_cast<Parse::TPTP::FileSourceRecord*>(rec);
      // cout << "Has FSR: " << frec->fileName << " " << frec->nameInFile << endl;

      // no premises from here
      // is this case even possible? I guess yes for a cnf input?
    } else {
      Parse::TPTP::InferenceSourceRecord* irec = static_cast<Parse::TPTP::InferenceSourceRecord*>(rec);
      // cout << "Has ISR: " << irec->name << endl;

      ik = inference_info.get(irec->name);
      inf = irec->name;

      if (ik > ICP) { // we want to load also the guys u came about from
        for (unsigned i = 0; i < irec->premises.size(); i++) {
          // cout << " p: " << irec->premises[i] << endl;
          todo.insert(irec->premises[i]);
        }
        premises = std::move(irec->premises);
      } else {
        // this is either clausification or the original problem was already in cnf
        // so we ignore the premises here and make such units source nodes
      }
    }

    Clause* cl = unitToClause(u);

    // cout << "CL:" << cl->toString() << endl;

    ALWAYS(clausesByNames.insert(uname,cl));
    if (premises.size() > 0) {
      ALWAYS(rememberedPremises.insert(uname,std::move(premises)));
    }

    tp->regNewClause(cl,uname,inf,ik);
    // cout << uname << " " << ik << " " << cl->toString() << endl;

    if (cl->isEmpty()) {
      tp->setEmpty(cl);
    }

    // cout << endl;
  }
  // cout << endl;

  // TODO: MANY things inside pp are still leaking
  delete pp;

  DHMap<vstring,Stack<vstring>>::Iterator it(rememberedPremises);
  while(it.hasNext()) {
    vstring uname;
    Stack<vstring>& premises = it.nextRef(uname);

    // cout << "uname " << uname << endl;
    Clause* child = clausesByNames.get(uname);

    for (unsigned i=0; i < premises.size(); i++) {
      vstring& prem = premises[i];

      // cout << "prem " << prem << endl;

      Clause* parent = clausesByNames.get(prem);

      tp->regChildParentPair(child,parent);
      /*
      cout << "pair" << endl;
      cout << child->toString() << endl;
      cout << parent->toString() << endl;
      cout << endl;
      */
    }
  }

  return tp;
}

void ProofTracer::init(const vstring& traceFileNames)
{
  ScopedLet<unsigned> temporarilyResetUnitCounter(Unit::_lastNumber,0);

  // TODO: make this handle more then one trace file, i.e., start by splitting traceFileNames into pieces (let's say comma-separated) and calling getUnits more than once
  ParsedProof* pp = getParsedProof(traceFileNames); // deals with the file
  _tp = prepareTracedProof(pp);                     // creates clauses out of the clausal part of pp, connects the clauses by pointers and discards the rest
  _tp->init();                                      // set the counters for proper event watching
}

