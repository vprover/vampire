
/*
 * File RecordingSatSolver.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file RecordingSatSolver.cpp
 * Implements class RecordingSatSolver.
 */

#include <sstream>

#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/StringUtils.hpp"

#include "SAT/SATClause.hpp"

#include "RecordingSatSolver.hpp"

namespace Test
{

///////////////////////
// RecordingSatSolver
//

#define REC(x) 

/**
 * Return header to be used for log outputs of this solver
 */
vstring RecordingSatSolver::getHdr() const
{
  CALL("RecordingSatSolver::getHdr");

  return "sat_"+Int::toHexString(reinterpret_cast<size_t>(this))+" ";
}

void RecordingSatSolver::addClauses(SATClauseIterator cit0, bool onlyPropagate,bool useInPartialModel)
{
  CALL("RecordingSatSolver::addClauses");

  SATClauseList* clauses = 0;
  SATClauseList::pushFromIterator(cit0, clauses);
  clauses = clauses->reverse();

  vostringstream clausesStm;
  SATClauseList::Iterator cit(clauses);
  while(cit.hasNext()) {
    SATClause* cl = cit.next();
    clausesStm << cl->toDIMACSString();
    if(cit.hasNext()) {
      clausesStm << "|";
    }
  }

  ASSERTION_VIOLATION_REP("Does not record useInPartialModel");

  REC("act=ac:op="<<onlyPropagate<<":clauses="<<clausesStm.str());

  _inner->addClauses(pvi(SATClauseList::DestructiveIterator(clauses)), onlyPropagate);
}

void RecordingSatSolver::randomizeAssignment()
{
  CALL("RecordingSatSolver::randomizeAssignment");

  REC("act=ra");

  _inner->randomizeAssignment();
}

void RecordingSatSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("RecordingSatSolver::ensureVarCnt");

  REC("act=evc:nwc="<<newVarCnt);

  _inner->ensureVarCnt(newVarCnt);
}

void RecordingSatSolver::addAssumption(SATLiteral lit, unsigned conflictCountLimit)
{
  CALL("RecordingSatSolver::addAssumption");

  REC("act=aa:litVar="<<lit.var()<<":litPol="<<lit.polarity()<<":ccl="<<conflictCountLimit);

  _inner->addAssumption(lit, conflictCountLimit);
}

void RecordingSatSolver::retractAllAssumptions()
{
  CALL("RecordingSatSolver::retractAllAssumptions");

  REC("act=raa");

  _inner->retractAllAssumptions();
}


///////////////////////
// SolverReplayer
//

SolverReplayer::ActionSpec::ActionSpec()
{
  CALL("SolverReplayer::ActionSpec::ActionSpec");

  rdr.registerEnumOption(&action, getReplayActionReader(), "act");
  rdr.registerUnsignedOption(&acOnlyPropagate, "op");
  rdr.registerStringOption(&acClausesStr, "clauses");
  rdr.registerUnsignedOption(&evcVarCnt, "nwc");
  rdr.registerUnsignedOption(&aaLitVar, "litVar");
  rdr.registerUnsignedOption(&aaLitPolarity, "litPol");
  rdr.registerUnsignedOption(&aaConflictCountLimit, "ccl");
}

SATClause* SolverReplayer::ActionSpec::readClause(vstring str)
{
  CALL("SolverReplayer::ActionSpec::readClause");

  static StringStack varStrings;
  varStrings.reset();
  StringUtils::splitStr(str.c_str(), ' ', varStrings);
  ASS_EQ(varStrings.top(), "0");
  varStrings.pop();

  static SATLiteralStack clauseLits;
  clauseLits.reset();

  StringStack::BottomFirstIterator vsit(varStrings);
  while(vsit.hasNext()) {
    vstring varSpec = vsit.next();
    int val;
    ALWAYS(Int::stringToInt(varSpec, val));
    clauseLits.push(SATLiteral(abs(val), val>0));
  }

  SATClause* res = SATClause::fromStack(clauseLits);
  return res;
}

void SolverReplayer::ActionSpec::readCommand(vstring str)
{
  CALL("SolverReplayer::ActionSpec::readCommand");

  if(!rdr.readOptions(str)) {
    ASSERTION_VIOLATION;
  }

  if(action==RA_ADD_CLAUSES) {
    static StringStack clauseStrings;
    clauseStrings.reset();
    StringUtils::splitStr(acClausesStr.c_str(), '|', clauseStrings);
    StringStack::BottomFirstIterator csit(clauseStrings);

    acClauses.reset();
    while(csit.hasNext()) {
      vstring clauseString = csit.next();
      acClauses.push(readClause(clauseString));
    }
  }
  else if(action==RA_ADD_ASSUMPTION) {
    aaLit = SATLiteral(aaLitVar, aaLitPolarity==1);
  }
}

const EnumReader<SolverReplayer::ReplayAction>& SolverReplayer::getReplayActionReader()
{
  CALL("SolverReplayer::getReplayActionReader");

  static bool initialized = false;
  static EnumReader<ReplayAction> rdr;
  if(!initialized) {
    initialized = true;
    rdr.addVal("ac", RA_ADD_CLAUSES);
    rdr.addVal("aa", RA_ADD_ASSUMPTION);
    rdr.addVal("ra", RA_RANDOMIZE_ASSIGNMENT);
    rdr.addVal("evc", RA_ENSURE_VAR_CNT);
    rdr.addVal("raa", RA_RETRACT_ALL_ASSUMPTIONS);
  }
  return rdr;
}

void SolverReplayer::performStep(vstring cmd)
{
  CALL("SolverReplayer::performStep");

  static ActionSpec aspec;
  aspec.readCommand(cmd);
  switch(aspec.action) {
  case RA_ADD_ASSUMPTION:
    _solver.addAssumption(aspec.aaLit, aspec.aaConflictCountLimit);
    break;
  case RA_ADD_CLAUSES:
    _solver.addClauses(aspec.getClauses(), aspec.acOnlyPropagate!=0);
    break;
  case RA_ENSURE_VAR_CNT:
    _solver.ensureVarCnt(aspec.evcVarCnt);
    break;
  case RA_RANDOMIZE_ASSIGNMENT:
    _solver.randomizeAssignment();
    break;
  case RA_RETRACT_ALL_ASSUMPTIONS:
    _solver.retractAllAssumptions();
    break;
  default:
    ASSERTION_VIOLATION;
  }
}

void SolverReplayer::runFromStream(istream& stm, vstring prefix)
{
  CALL("SolverReplayer::runFromStream");

  size_t prefLen = prefix.length();
  do {
    vstring line;
    getline(stm, line);
    if(line.substr(0,prefLen)!=prefix) {
      continue;
    }
    vstring cmd = line.substr(prefLen);
    performStep(cmd);
  } while(!stm.eof());
}

}
