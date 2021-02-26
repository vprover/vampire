
/*
 * File ForwardSubsumptionAndResolution.cpp.
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
 * @file ForwardSubsumptionAndResolution.cpp
 * Implements class ForwardSubsumptionAndResolution.
 */


#include "Lib/VirtualIterator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/List.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include <fstream>
#include "Shell/TPTPPrinter.hpp"

#include "ForwardSubsumptionAndResolution.hpp"


namespace Inferences
{
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;



#define CHECK_SMT_SUBSUMPTION 0

static ForwardSubsumptionAndResolution* fwsubsandres_instance = nullptr;

ForwardSubsumptionAndResolution::ForwardSubsumptionAndResolution(bool subsumptionResolution)
  : _subsumptionResolution(subsumptionResolution)
{
  CALL("ForwardSubsumptionAndResolution::ForwardSubsumptionAndResolution");
  vstring const& logfile = env.options->subsumptionLogfile();
  if (!logfile.empty()) {
    BYPASSING_ALLOCATOR;
    m_logger = make_unique<SubsumptionLogger>(logfile);
  }
}

ForwardSubsumptionAndResolution::~ForwardSubsumptionAndResolution()
{
  if (m_logger) {
    BYPASSING_ALLOCATOR;
    m_logger.reset();
  }
}

void ForwardSubsumptionAndResolution::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardSubsumptionAndResolution::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex=static_cast<UnitClauseLiteralIndex*>(
	  _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE) );
  _fwIndex=static_cast<FwSubsSimplifyingLiteralIndex*>(
	  _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE) );
  if (fwsubsandres_instance != nullptr && fwsubsandres_instance != this) {
    VAMPIRE_EXCEPTION;
  }
  fwsubsandres_instance = this;
}

ForwardSubsumptionAndResolution* ForwardSubsumptionAndResolution::getInstance()
{
  return fwsubsandres_instance;
}

void ForwardSubsumptionAndResolution::detach()
{
  CALL("ForwardSubsumptionAndResolution::detach");
  _unitIndex=0;
  _fwIndex=0;
  _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


struct ClauseMatches {
  CLASS_NAME(ForwardSubsumptionAndResolution::ClauseMatches);
  USE_ALLOCATOR(ClauseMatches);

private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  ClauseMatches(const ClauseMatches&);
  ClauseMatches& operator=(const ClauseMatches&);
public:
  ClauseMatches(Clause* cl) : _cl(cl), _zeroCnt(cl->length())
  {
    unsigned clen=_cl->length();
    _matches=static_cast<LiteralList**>(ALLOC_KNOWN(clen*sizeof(void*), "Inferences::ClauseMatches"));
    for(unsigned i=0;i<clen;i++) {
      _matches[i]=0;
    }
  }
  ~ClauseMatches()
  {
    unsigned clen=_cl->length();
    for(unsigned i=0;i<clen;i++) {
      LiteralList::destroy(_matches[i]);
    }
    DEALLOC_KNOWN(_matches, clen*sizeof(void*), "Inferences::ClauseMatches");
  }

  void addMatch(Literal* baseLit, Literal* instLit)
  {
    addMatch(_cl->getLiteralPosition(baseLit), instLit);
  }
  void addMatch(unsigned bpos, Literal* instLit)
  {
    if(!_matches[bpos]) {
      _zeroCnt--;
    }
    LiteralList::push(instLit,_matches[bpos]);
  }
  void fillInMatches(LiteralMiniIndex* miniIndex)
  {
    unsigned blen=_cl->length();

    for(unsigned bi=0;bi<blen;bi++) {
      LiteralMiniIndex::InstanceIterator instIt(*miniIndex, (*_cl)[bi], false);
      while(instIt.hasNext()) {
	Literal* matched=instIt.next();
	addMatch(bi, matched);
      }
    }
  }
  bool anyNonMatched() { return _zeroCnt; }

  Clause* _cl;
  unsigned _zeroCnt;
  LiteralList** _matches;

  class ZeroMatchLiteralIterator
  {
  public:
    ZeroMatchLiteralIterator(ClauseMatches* cm)
    : _lits(cm->_cl->literals()), _mlists(cm->_matches), _remaining(cm->_cl->length())
    {
      if(!cm->_zeroCnt) {
	_remaining=0;
      }
    }
    bool hasNext()
    {
      while(_remaining>0 && *_mlists) {
	_lits++; _mlists++; _remaining--;
      }
      return _remaining;
    }
    Literal* next()
    {
      _remaining--;
      _mlists++;
      return *(_lits++);
    }
  private:
    Literal** _lits;
    LiteralList** _mlists;
    unsigned _remaining;
  };
};


typedef Stack<ClauseMatches*> CMStack;

/*
bool isSubsumed(Clause* cl, CMStack& cmStore)
{
  CALL("isSubsumed");

  CMStack::Iterator csit(cmStore);
  while(csit.hasNext()) {
    ClauseMatches* clmatches;
    clmatches=csit.next();
    Clause* mcl=clmatches->_cl;

    if(clmatches->anyNonMatched()) {
      continue;
    }

    if(MLMatcher::canBeMatched(mcl,cl,clmatches->_matches,0)) {
      return true;
    }
  }
  return false;
}
*/

Clause* ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(Clause* cl, Literal* lit, Clause* baseClause)
{
  CALL("ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause");
  int clen = cl->length();
  int nlen = clen-1;

  Clause* res = new(nlen) Clause(nlen,
      SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, cl, baseClause));

  int next = 0;
  bool found=false;
  for(int i=0;i<clen;i++) {
    Literal* curr=(*cl)[i];
    //As we will apply subsumption resolution after duplicate literal
    //deletion, the same literal should never occur twice.
    ASS(curr!=lit || !found);
    if(curr!=lit || found) {
	(*res)[next++] = curr;
    } else {
      found=true;
    }
  }

  return res;
}

bool checkForSubsumptionResolution(Clause* cl, ClauseMatches* cms, Literal* resLit)
{
  Clause* mcl=cms->_cl;
  unsigned mclen=mcl->length();

  ClauseMatches::ZeroMatchLiteralIterator zmli(cms);
  if(zmli.hasNext()) {
    while(zmli.hasNext()) {
      Literal* bl=zmli.next();
//      if( !resLit->couldBeInstanceOf(bl, true) ) {
      if( ! MatchingUtils::match(bl, resLit, true) ) {
	return false;
      }
    }
  } else {
    bool anyResolvable=false;
    for(unsigned i=0;i<mclen;i++) {
//      if(resLit->couldBeInstanceOf((*mcl)[i], true)) {
      if( MatchingUtils::match((*mcl)[i], resLit, true) ) {
	anyResolvable=true;
	break;
      }
    }
    if(!anyResolvable) {
      return false;
    }
  }

  return MLMatcher::canBeMatched(mcl,cl,cms->_matches,resLit);
}

class SubsumptionLogger
{
  private:
    std::ofstream m_logfile;
    TPTPPrinter m_tptp;  // this needs to be a member so we get the type definitions only once at the beginning
    unsigned int m_seq;  // sequence number of logged inferences
  public:
    CLASS_NAME(SubsumptionLogger);
    USE_ALLOCATOR(SubsumptionLogger);
    SubsumptionLogger(vstring logfile_path);
    void log(Clause* side_premise, Clause* main_premise, bool isSubsumed, MLMatchStats const* opt_stats);
    void flush() { m_logfile.flush(); }
};

SubsumptionLogger::SubsumptionLogger(vstring logfile_path)
  : m_logfile{}
  , m_tptp{&m_logfile}
  , m_seq{1}
{
  CALL("SubsumptionLogger::SubsumptionLogger");
  m_logfile.open(logfile_path.c_str());
  ASS(m_logfile.is_open());
}

void SubsumptionLogger::log(Clause* side_premise, Clause* main_premise, bool isSubsumed, MLMatchStats const* opt_stats)
{
  vstringstream id_stream;
  id_stream
    << m_seq << "_"
    // << main_premise->number() << "_"  // main premise first because that increases during the run
    // << side_premise->number() << "_"
    << (isSubsumed ? "success" : "failure");
  vstring id = id_stream.str();

  m_logfile << "\% Begin Inference \"FS-" << id << "\"\n";

  m_logfile << "\% Info: "
            // << "{ \"seq\": " << m_seq
            << "{ \"side_premise\": " << side_premise->number()
            << ", \"main_premise\": " << main_premise->number();
  if (opt_stats) {
    m_logfile << ", \"stats\": " << (*opt_stats);
    // m_logfile << "\% Stats: " << (*opt_stats) << '\n';
  }
  m_logfile << " }\n";

  m_tptp.printWithRole("side_premise_" + id, "hypothesis", side_premise, false);  // subsumer
  m_tptp.printWithRole("main_premise_" + id, "hypothesis", main_premise, false);  // subsumed (if isSubsumed == 1)
  m_logfile << "\% End Inference \"FS-" << id << "\"\n\%" << std::endl;

  m_seq += 1;
}

void ForwardSubsumptionAndResolution::printStats(std::ostream& out)
{
  if (m_logger) {
    m_logger->flush();
  }
  out << "\% Subsumption MLMatcher Statistics\n\% (numDecisions Frequency Successes)\n";
  for (size_t n = 0; n < m_numDecisions_frequency.size(); ++n) {
    if (m_numDecisions_frequency[n] > 0) {
      out << "\% " << n << ' ' << m_numDecisions_frequency[n] << ' ' << m_numDecisions_successes[n] << '\n';
    }
  }
}


bool ForwardSubsumptionAndResolution::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardSubsumptionAndResolution::perform");

  Clause* resolutionClause=0;

  unsigned clen=cl->length();
  if(clen==0) {
    return false;
  }

  TimeCounter tc_fs(TC_FORWARD_SUBSUMPTION);

  bool result = false;

  Clause::requestAux();

  static CMStack cmStore(64);
  ASS(cmStore.isEmpty());

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_unitIndex->getGeneralizations( (*cl)[li], false, false);
    while(rit.hasNext()) {
      Clause* premise=rit.next().clause;
      if(premise->hasAux()) {
	continue;
      }
      premise->setAux(0);
      if(ColorHelper::compatible(cl->color(), premise->color()) ) {
        premises = pvi( getSingletonIterator(premise) );
        env.statistics->forwardSubsumed++;
        ASS_LE(premise->weight(), cl->weight());
        result = true;
#if CHECK_SMT_SUBSUMPTION
        if (!smtsubs.checkSubsumption(premise, cl)) {
          std::cerr << "\% ***WRONG RESULT OF SMT-SUBSUMPTION***    UNIT expecting 1" << std::endl;
          std::cerr << "\% premise = " << premise->toString() << std::endl;
          std::cerr << "\% cl = " << cl->toString() << std::endl;
        }
#endif
        // NOTE: we do not care about outputting the inference here, since this branch is not a target where we want to use SMT-Subsumption.
        goto fin;
      }
    }
  }

  {
  LiteralMiniIndex miniIndex(cl);

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_fwIndex->getGeneralizations( (*cl)[li], false, false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      Clause* mcl=res.clause;
      if(mcl->hasAux()) {
        //we've already checked this clause
        continue;
      }
      unsigned mlen=mcl->length();
      ASS_G(mlen,1);

      ClauseMatches* cms=new ClauseMatches(mcl);
      mcl->setAux(cms);
      cmStore.push(cms);
      //      cms->addMatch(res.literal, (*cl)[li]);
      //      cms->fillInMatches(&miniIndex, res.literal, (*cl)[li]);
      cms->fillInMatches(&miniIndex);

      if(cms->anyNonMatched()) {
        continue;
      }

      if (mcl->weight() > cl->weight()) {
        RSTAT_CTR_INC("fw subsumption impossible due to weight");
      }

      RSTAT_CTR_INC("MLSubsumption Calls");
      bool isSubsumed =
        MLMatcher::canBeMatched(mcl,cl,cms->_matches,0)
        && ColorHelper::compatible(cl->color(), mcl->color());

// Enable if you want to log *every* subsumption instance
#if 0
      if (m_logger) {
        m_logger->log(mcl, cl, isSubsumed, MLMatcher::getStaticStats());
      }
#endif

      m_seq += 1;
      m_seq_output += 1;
      auto stats = MLMatcher::getStaticStats();
      // env.beginOutput();
      // // env.out() << "\% MLMatcher(" << mcl->number() << "," << cl->number() << ")\n";
      // // env.out() << "\% mcl = " << mcl->toString() << "\n";
      // // env.out() << "\%  cl = " << cl->toString() << "\n";
      // env.out() << "\% Subsumption "
      //           << "{ \"seq\": " << seq
      //           << ", \"mcl\": " << mcl->number()
      //           << ", \"cl\": " << cl->number()
      //           << ", \"stats\": " << MLMatcher::getStaticStats()
      //           << " }\n";
      // env.endOutput();
      if (stats.numDecisions >= 100) {
        if (m_logger) {
          // Log "interesting" subsumption instances
          m_logger->log(mcl, cl, isSubsumed, &stats);
        }
        env.beginOutput();
        env.out() << "\% Subsumption(" << mcl->number() << "," << cl->number() << ")\n";
        env.out() << "\% mcl = " << mcl->toString() << "\n";
        env.out() << "\%  cl = " << cl->toString() << "\n";
        env.out() << "\% Subsumption "
                  << "{ \"seq\": " << m_seq
                  << ", \"mcl\": " << mcl->number()
                  << ", \"cl\": " << cl->number()
                  << ", \"stats\": " << stats
                  << " }\n\%\n";
        env.endOutput();
      }
      if (stats.numDecisions >= m_numDecisions_frequency.size()) {
        size_t new_size = std::max(std::max(256ul, (size_t)stats.numDecisions+1), m_numDecisions_frequency.size() * 2);
        m_numDecisions_frequency.resize(new_size, 0);
        m_numDecisions_successes.resize(new_size, 0);
      }
      m_numDecisions_frequency[stats.numDecisions] += 1;
      if (stats.result) {
        m_numDecisions_successes[stats.numDecisions] += 1;
      }

#if CHECK_SMT_SUBSUMPTION
        if (smtsubs.checkSubsumption(mcl, cl) != isSubsumed) {
          std::cerr << "\% ***WRONG RESULT OF SMT-SUBSUMPTION***    MULTI expecting " << isSubsumed << std::endl;
          std::cerr << "\% mcl = " << mcl->toString() << std::endl;
          std::cerr << "\%  cl = " <<  cl->toString() << std::endl;
        };
#endif

      if (isSubsumed) {
        premises = pvi( getSingletonIterator(mcl) );
        env.statistics->forwardSubsumed++;
        ASS_LE(mcl->weight(), cl->weight());
        result = true;
        goto fin;
      }
    }
  }

  tc_fs.stop();

  // if (m_seq_output > 10000) {
  //   m_seq_output = 0;
  //   env.beginOutput();
  //   printStats(env.out());
  //   env.endOutput();
  // }

  if(!_subsumptionResolution) {
    goto fin;
  }

  {
    TimeCounter tc_fsr(TC_FORWARD_SUBSUMPTION_RESOLUTION);

    for(unsigned li=0;li<clen;li++) {
      Literal* resLit=(*cl)[li];
      SLQueryResultIterator rit=_unitIndex->getGeneralizations( resLit, true, false);
      while(rit.hasNext()) {
	Clause* mcl=rit.next().clause;
	if(ColorHelper::compatible(cl->color(), mcl->color())) {
	  resolutionClause=generateSubsumptionResolutionClause(cl,resLit,mcl);
	  env.statistics->forwardSubsumptionResolution++;
	  premises = pvi( getSingletonIterator(mcl) );
	  replacement = resolutionClause;
	  result = true;
	  goto fin;
	}
      }
    }

    {
      CMStack::Iterator csit(cmStore);
      while(csit.hasNext()) {
	ClauseMatches* cms=csit.next();
	for(unsigned li=0;li<clen;li++) {
	  Literal* resLit=(*cl)[li];
	  if(checkForSubsumptionResolution(cl, cms, resLit) && ColorHelper::compatible(cl->color(), cms->_cl->color()) ) {
	    resolutionClause=generateSubsumptionResolutionClause(cl,resLit,cms->_cl);
	    env.statistics->forwardSubsumptionResolution++;
	    premises = pvi( getSingletonIterator(cms->_cl) );
	    replacement = resolutionClause;
	    result = true;
	    goto fin;
	  }
	}
      }
    }

    for(unsigned li=0;li<clen;li++) {
      Literal* resLit=(*cl)[li];	//resolved literal
      SLQueryResultIterator rit=_fwIndex->getGeneralizations( resLit, true, false);
      while(rit.hasNext()) {
	SLQueryResult res=rit.next();
	Clause* mcl=res.clause;

	if(mcl->hasAux()) {
	  //we have already examined this clause
	  continue;
	}

	ClauseMatches* cms=new ClauseMatches(mcl);
	res.clause->setAux(cms);
	cmStore.push(cms);
	cms->fillInMatches(&miniIndex);

	if(checkForSubsumptionResolution(cl, cms, resLit) && ColorHelper::compatible(cl->color(), cms->_cl->color())) {
	  resolutionClause=generateSubsumptionResolutionClause(cl,resLit,cms->_cl);
	  env.statistics->forwardSubsumptionResolution++;
          premises = pvi( getSingletonIterator(cms->_cl) );
          replacement = resolutionClause;
          result = true;
	  goto fin;
	}

      }
    }
  }
  }

fin:
  Clause::releaseAux();
  while(cmStore.isNonEmpty()) {
    delete cmStore.pop();
  }
  return result;
}

}
