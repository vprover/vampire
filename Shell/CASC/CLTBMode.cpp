/**
 * @file CLTBMode.cpp
 * Implements class CLTBMode.
 */

#include <fstream>
#include <cstdlib>
#include <csignal>
#include <sstream>

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Sys/SyncPipe.hpp"

#include "Shell/Options.hpp"
#include "Shell/Normalisation.hpp"
#include "Saturation/ProvingHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Parse/TPTP.hpp"

#include "CASCMode.hpp"

#include "CLTBMode.hpp"

#define SLOWNESS 1.15

using namespace Shell::CASC;
using namespace std;
using namespace Lib;
using namespace Lib::Sys;
using namespace Saturation;

void CLTBMode::perform()
{
  CALL("CLTBMode::perform");

  if(env.options->inputFile()=="") {
    USER_ERROR("Input file must be specified for cltb mode");
  }

  string line;
  ifstream in(env.options->inputFile().c_str());
  if(in.fail()) {
    USER_ERROR("Cannot open input file: "+env.options->inputFile());
  }

  while(!in.eof()) {
    stringstream singleInst;
    bool ready = false;
    while(!in.eof()) {
      std::getline(in, line);
      singleInst<<line<<endl;
      if(line=="% SZS end BatchProblems") {
	ready = true;
	break;
      }
    }
    if(!ready) { break; }
    Shell::CASC::CLTBMode ltbm;
    stringstream childInp(singleInst.str());
    ltbm.perform(childInp);
  }
}

/**
 * This function runs the batch master process and spawns the child master processes
 *
 * In this function we:
 * 1) read the batch file
 * 2) load the common axioms and put them into a SInE selector
 * 3) run a child master process for each problem (sequentially)
 */
void CLTBMode::perform(istream& batchFile)
{
  CALL("CLTBMode::perform");

  readInput(batchFile);
//  env.options->setTimeLimitInSeconds(overallTimeLimit);
  env.options->setTimeLimitInSeconds(0);

  loadIncludes();

  int solvedCnt=0;

  StringPairStack::BottomFirstIterator probs(problemFiles);
  while(probs.hasNext()) {
    StringPair res=probs.next();

    string probFile=res.first;
    string outFile=res.second;

    pid_t child=Multiprocessing::instance()->fork();
    if(!child) {
      CLTBProblem prob(this, probFile, outFile);
      prob.perform();

      //the prob.perform() function should never return
      ASSERTION_VIOLATION;
    }
    env.beginOutput();
    env.out()<<"% SZS status Started for "<<probFile<<endl;
    env.out()<<"solver pid "<<child<<endl;
    env.endOutput();
    int resValue;
    try {
      pid_t finishedChild=Multiprocessing::instance()->waitForChildTermination(resValue);
      ASS_EQ(finishedChild, child);
    } catch(SystemFailException& ex) {
      cerr << "SystemFailException at batch level" << endl;
      ex.cry(cerr);
    }

    env.beginOutput();
    if(!resValue) {
      env.out()<<"% SZS status Theorem for "<<probFile<<endl;
      solvedCnt++;
    }
    else {
      env.out()<<"% SZS status GaveUp for "<<probFile<<endl;
    }
    env.out()<<"% SZS status Ended for "<<probFile<<endl;
    env.endOutput();

    Timer::syncClock();
  }
  env.beginOutput();
  env.out()<<"Solved "<<solvedCnt<<" out of "<<problemFiles.size()<<endl;
  env.endOutput();
}

void CLTBMode::loadIncludes()
{
  CALL("CLTBMode::loadIncludes");

  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    theoryAxioms=0;
    StringList::Iterator iit(theoryIncludes);
    while(iit.hasNext()) {
      string fname=env.options->includeFileName(iit.next());
      ifstream inp(fname.c_str());
      if(inp.fail()) {
        USER_ERROR("Cannot open included file: "+fname);
      }
      Parse::TPTP parser(inp);
      parser.parse();
      UnitList* funits = parser.units();
      if(parser.containsConjecture()) {
	USER_ERROR("Axiom file "+fname+" contains a conjecture.");
      }

      UnitList::Iterator fuit(funits);
      while(fuit.hasNext()) {
	fuit.next()->markIncluded();
      }
      theoryAxioms=UnitList::concat(funits,theoryAxioms);
    }
  }

  {
    TimeCounter tc(TC_PREPROCESSING);
    env.statistics->phase=Statistics::PROPERTY_SCANNING;

    property = Property::scan(theoryAxioms);
  }

//  {
//    TimeCounter tc(TC_SINE_SELECTION);
//    env.statistics->phase=Statistics::SINE_SELECTION;
//
//    theorySelector.initSelectionStructure(theoryAxioms);
//  }
  env.statistics->phase=Statistics::UNKNOWN_PHASE;
}

void CLTBMode::readInput(istream& in)
{
  CALL("CLTBMode::readInput");

  string line, word;

  std::getline(in, line);
  if(line!="% SZS start BatchConfiguration") {
    USER_ERROR("\"% SZS start BatchConfiguration\" expected, \""+line+"\" found.");
  }

  in>>word;
  if(word!="division.category") {
    USER_ERROR("\"division.category\" expected, \""+word+"\" found.");
  }
  in>>category;

  in>>word;
  if(word!="output.required") {
    USER_ERROR("\"output.required\" expected, \""+word+"\" found.");
  }
  for(in>>word; word!="output.desired"; in>>word) {}

  if(word!="output.desired") {
    USER_ERROR("\"output.desired\" expected.");
  }
  questionAnswering = false;
  for(in>>word; word!="limit.time.problem.wc"; in>>word) {
    if(word=="Answer") {
      questionAnswering = true;
    }
  }
  if(questionAnswering) {
    env.options->setQuestionAnswering(Options::QA_ANSWER_LITERAL);
  }
  else {
    env.options->setQuestionAnswering(Options::QA_OFF);
  }

  if(word!="limit.time.problem.wc") {
    USER_ERROR("\"limit.time.problem.wc\" expected.");
  }
  in>>problemTimeLimit;

//  in>>word;
//  if(word!="limit.time.overall.wc") {
//    USER_ERROR("\"limit.time.overall.wc\" expected, \""+word+"\" found.");
//  }
//  in>>overallTimeLimit;

  std::getline(in, line);
  while(!in.eof() && line=="") { std::getline(in, line); }
  if(line!="% SZS end BatchConfiguration") {
    USER_ERROR("\"% SZS end BatchConfiguration\" expected, \""+line+"\" found.");
  }
  std::getline(in, line);
  if(line!="% SZS start BatchIncludes") {
    USER_ERROR("\"% SZS start BatchIncludes\" expected, \""+line+"\" found.");
  }

  theoryIncludes=0;
  for(std::getline(in, line); line[0]!='%' && !in.eof(); std::getline(in, line)) {
    size_t first=line.find_first_of('\'');
    size_t last=line.find_last_of('\'');
    if(first==string::npos || first==last) {
      USER_ERROR("Include specification must contain the file name enclosed in the ' characters:\""+line+"\".");
    }
    ASS_G(last,first);
    string fname=line.substr(first+1, last-first-1);
    StringList::push(fname, theoryIncludes);
  }

  while(!in.eof() && line=="") { std::getline(in, line); }
  if(line!="% SZS end BatchIncludes") {
    USER_ERROR("\"% SZS end BatchIncludes\" expected, \""+line+"\" found.");
  }
  std::getline(in, line);
  if(line!="% SZS start BatchProblems") {
    USER_ERROR("\"% SZS start BatchProblems\" expected, \""+line+"\" found.");
  }

  for(std::getline(in, line); line[0]!='%' && !in.eof(); std::getline(in, line)) {
    size_t spc=line.find(' ');
    size_t lastSpc=line.find(' ', spc+1);
    if(spc==string::npos || spc==0 || spc==line.length()-1) {
      USER_ERROR("Two file names separated by a single space expected:\""+line+"\".");
    }
    string inp=line.substr(0,spc);
    string outp=line.substr(spc+1, lastSpc-spc-1);
    problemFiles.push(make_pair(inp, outp));
  }

  while(!in.eof() && line=="") { std::getline(in, line); }
  if(line!="% SZS end BatchProblems") {
    USER_ERROR("\"% SZS end BatchProblems\" expected, \""+line+"\" found.");
  }
}


//////////////////////////////////////////
// CLTBProblem
//////////////////////////////////////////

string CLTBProblem::problemFinishedString = "##Problem finished##vn;3-d-ca-12=1;'";

CLTBProblem::CLTBProblem(CLTBMode* parent, string problemFile, string outFile)
: parent(parent), problemFile(problemFile), outFile(outFile), property(new Property(*parent->property))
{
}

/**
 * This function should use the runSchedule function to prove the problem.
 * Once the problem is proved, the @b runSchedule function does not return
 * and the process terminates.
 *
 * The properties of the problem are in the @b property field.
 * The name of problem category (MZR, SMO or CYC) is in @b parent->category.
 *
 * If a slice contains sine_selection value different from off, theory axioms
 * will be selected using SInE from the common axioms included in the batch file
 * (all problem axioms, including the included ones, will be used as a base
 * for this selection).
 *
 * If the sine_selection is off, all the common axioms will be just added to the
 * problem axioms. All this is done in the @b runChild(Options&) function.
 */
void CLTBProblem::performStrategy()
{
  CALL("CLTBProblem::performStrategy");

  unsigned atoms = property->atoms();
  unsigned prop = property->props();
  cout << "Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  Schedule quick;
  Schedule fallback;
  StrategySet usedSlices;

  fallback.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_600");
  fallback.push("ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_600");
  fallback.push("dis+1003_8_bms=on:ecs=on:lcm=predicate:nwc=3.0:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:updr=off_600");
  fallback.push("dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_600");
  fallback.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_300");
  fallback.push("dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_300");
  fallback.push("dis+10_3:1_bs=off:br=off:drc=off:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:st=5.0:sac=on:spo=on:spl=backtracking:sp=reverse_arity:urr=on_900");
  fallback.push("dis+1011_1_bd=off:bs=off:drc=off:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_300");
  fallback.push("ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_300");
  fallback.push("ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_300");
  fallback.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300");
  fallback.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_300");
  fallback.push("dis+1002_8:1_bd=off:bs=unit_only:bsr=on:ep=on:flr=on:nwc=10:sswsr=on:sac=on:sgo=on:sio=off:sfv=off_300");
  fallback.push("dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_600");
  fallback.push("dis-2_5:4_bd=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=2:sswsr=on:sos=on:sagn=off:sac=on:spo=on:sp=reverse_arity_300");
  fallback.push("lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_300");
  fallback.push("ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_300");
  fallback.push("ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_300");
  fallback.push("dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300");
  fallback.push("dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_300");
  fallback.push("dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_300");
  fallback.push("dis+1_14_bsr=unit_only:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sd=10:ss=included:st=1.5:sagn=off:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_1200");
  fallback.push("lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_300");
  fallback.push("lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_1200");
  fallback.push("lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:ss=included:sio=off:spl=backtracking_600");
  fallback.push("dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_300");
  fallback.push("dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_600");
  fallback.push("dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_300");
  fallback.push("dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_300");
  fallback.push("ins+1010_4_bs=unit_only:flr=on:gsp=input_only:igbrr=0.9:igrr=1/128:igrp=200:igrpq=1.3:igwr=on:nwc=5:ptb=off:ssec=off:spl=off_300");
  fallback.push("dis+11_14_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=10:ssec=off:sos=on:sagn=off:sac=on:sgo=on:spo=on:sp=reverse_arity_300");
  fallback.push("ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_300");
  fallback.push("ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_300");
  fallback.push("lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300");
  fallback.push("ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_300");
  fallback.push("dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_300");
  fallback.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_600");
  fallback.push("dis+1011_14_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:nicw=on:sswn=on:sgo=on:spo=on:sp=reverse_arity_300");
  fallback.push("lrs+1_3:1_bd=off:bs=off:bsr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:spl=backtracking_300");
  fallback.push("dis+1011_64_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:spl=backtracking:sp=occurrence_300");
  fallback.push("dis-1010_5_bs=off:drc=off:ep=on:gsp=input_only:gs=on:nwc=2.5:ptb=off:ssec=off:sac=on:sgo=on:sio=off:swb=on:sp=reverse_arity_300");
  fallback.push("dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300");
  fallback.push("ott+2_3_bs=unit_only:bsr=unit_only:cond=fast:fde=none:gsp=input_only:nwc=1.2:ptb=off:ssec=off:sfv=off:sp=reverse_arity_300");
  fallback.push("ott+11_14_bd=off:bs=off:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sagn=off:spo=on:spl=backtracking:sp=occurrence:updr=off_300");
  fallback.push("lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_300");
  fallback.push("lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_300");
  fallback.push("lrs+11_20_bd=off:bs=off:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:sd=2:ss=axioms:st=2.0:sgo=on:spo=on:swb=on_900");
  fallback.push("dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_600");

  if (atoms > 2000000) {
    quick.push("dis+1_14_bsr=unit_only:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sd=10:ss=included:st=1.5:sagn=off:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_900");
    quick.push("dis+10_3:1_bs=off:br=off:drc=off:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:st=5.0:sac=on:spo=on:spl=backtracking:sp=reverse_arity:urr=on_900");
  }
  else if (prop == 131087) {
    if (atoms > 300000) {
      quick.push("ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_49");
      quick.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_79");
      quick.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_123");
      quick.push("dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_98");
      quick.push("ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_31");
      quick.push("dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_46");
      quick.push("dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_91");
      quick.push("ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_44");
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_37");
      quick.push("dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_46");
      quick.push("ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_213");
      quick.push("dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_82");
      quick.push("ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_123");
      quick.push("lrs+11_20_bd=off:bs=off:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:stl=90:sd=2:ss=axioms:st=2.0:sgo=on:spo=on:swb=on_544");
    }
    else if (atoms>150000) {
      quick.push("dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_20");
      quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_181");
      quick.push("dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_15");
      quick.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_161");
      quick.push("dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_19");
      quick.push("lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_23");
      quick.push("lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_20");
      quick.push("dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_93");
      quick.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_194");
      quick.push("ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_155");
      quick.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_169");
      quick.push("lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_882");
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_23");
    }
    else if (atoms > 80000) {
      quick.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_26");
      quick.push("ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_14");
      quick.push("lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=30:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_10");
      quick.push("dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_14");
      quick.push("dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_86");
      quick.push("dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_27");
      quick.push("dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_16");
      quick.push("dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_21");
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_12");
      quick.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_19");
      quick.push("dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_7");
      quick.push("ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_19");
      quick.push("dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_7");
      quick.push("dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_66");
      quick.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_144");
      quick.push("dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_43");
      quick.push("ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_71");
      quick.push("lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_91");
      quick.push("ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_290");
      quick.push("ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_150");
      quick.push("dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_172");
      quick.push("lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sd=2:ss=included:sio=off:spl=backtracking_182");
      quick.push("dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_344");
      quick.push("lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_8");
      quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_77");
    }
    else {
      quick.push("lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=30:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_3");
      quick.push("dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_4");
      quick.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_16");
      quick.push("dis-2_5:4_bd=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=2:sswsr=on:sos=on:sagn=off:sac=on:spo=on:sp=reverse_arity_4");
      quick.push("ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_61");
      quick.push("dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_7");
      quick.push("dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_2");
      quick.push("lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_17");
      quick.push("dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_89");
      quick.push("dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_6");
      quick.push("ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_7");
      quick.push("ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_48");
      quick.push("dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_23");
      quick.push("dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_9");
      quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_86");
      quick.push("dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_9");
      quick.push("ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_7");
      quick.push("lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_134");
      quick.push("dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_36");
      quick.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_91");
      quick.push("dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_70");
      quick.push("ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_73");
      quick.push("dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_29");
      quick.push("dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_94");
      quick.push("ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_76");
      quick.push("ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_95");
      quick.push("lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:stl=30:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_277");
      quick.push("lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_878");
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_7");
      quick.push("lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_8");
      quick.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_135");
    }
  }
  else  {
    quick.push("ott+1_2_bs=unit_only:cond=on:drc=off:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_20");
    quick.push("tab+10_1_ep=RST:ss=axioms:spl=off:tbsr=off:tgawr=1/16:tglr=4/1:tipr=off:tlawr=1/50_6");
    quick.push("dis+1011_3_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ssec=off:sos=on:spo=on:sp=reverse_arity_3");
    quick.push("dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_12");
    quick.push("dis+10_16_bs=off:drc=off:nwc=1.5:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_3");
    quick.push("dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_2");
    quick.push("dis+1011_14_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:nicw=on:sswn=on:sgo=on:spo=on:sp=reverse_arity_8");
    quick.push("dis+1011_1_bd=off:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sgt=7:ss=axioms:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_1");
    quick.push("dis+11_14_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=10:ssec=off:sos=on:sagn=off:sac=on:sgo=on:spo=on:sp=reverse_arity_9");
    quick.push("ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_35");
    quick.push("ott+1011_3:1_bs=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_45");
    quick.push("dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_2");
    quick.push("dis+1011_1_bs=off:cond=fast:gs=on:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sgo=on:spo=on:swb=on:sp=reverse_arity_3");
    quick.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_46");
    quick.push("dis+1011_64_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:spl=backtracking:sp=occurrence_15");
    quick.push("tab+10_1_gsp=input_only:spl=off:tbsr=off:tfsr=off:tgawr=1/128:tglr=1/7:tipr=off:tlawr=1/2_2");
    quick.push("dis+1011_1_bd=off:bs=off:drc=off:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_60");
    quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_1");
    quick.push("ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_496");
    quick.push("ott+11_14_bd=off:bs=off:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sagn=off:spo=on:spl=backtracking:sp=occurrence:updr=off_101");
    quick.push("dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_200");
    quick.push("lrs+1_3:1_bd=off:bs=off:bsr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:stl=30:sos=on:sac=on:sio=off:spo=on:spl=backtracking_153");
    quick.push("ott+2_3_bs=unit_only:bsr=unit_only:cond=fast:fde=none:gsp=input_only:nwc=1.2:ptb=off:ssec=off:sfv=off:sp=reverse_arity_206");
    quick.push("ins+1010_4_bs=unit_only:flr=on:gsp=input_only:igbrr=0.9:igrr=1/128:igrp=200:igrpq=1.3:igwr=on:nwc=5:ptb=off:ssec=off:spl=off_274");
    quick.push("dis-1002_5:1_bs=unit_only:bsr=unit_only:flr=on:gsp=input_only:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sswn=on:sos=on:spo=on:swb=on:sp=occurrence_3");
    quick.push("dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_107");
  }

  int remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return;
  }
  if (runSchedule(quick,usedSlices,false)) {
    return;
  }
  remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return;
  }
  runSchedule(fallback,usedSlices,true);
}

void CLTBProblem::perform()
{
  CALL("CLTBProblem::perform");

  System::registerForSIGHUPOnParentDeath();

  env.timer->reset();
  env.timer->start();
  env.timer->makeChildrenIncluded();
  TimeCounter::reinitialize();

  env.options->setTimeLimitInSeconds(parent->problemTimeLimit);
  env.options->setInputFile(problemFile);

  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    ifstream inp(problemFile.c_str());
    if(inp.fail()) {
      USER_ERROR("Cannot open problem file: "+problemFile);
    }
    Parse::TPTP parser(inp);
    List<string>::Iterator iit(parent->theoryIncludes);
    while (iit.hasNext()) {
      parser.addForbiddenInclude(iit.next());
    }
    parser.parse();
    probUnits = parser.units();
    UIHelper::setConjecturePresence(parser.containsConjecture());
  }

  {
    TimeCounter tc(TC_PREPROCESSING);
    env.statistics->phase=Statistics::PROPERTY_SCANNING;

    property->add(probUnits);
    env.statistics->phase=Statistics::UNKNOWN_PHASE;
    //concat with theory axioms
    probUnits=UnitList::concat(probUnits, parent->theoryAxioms);

    if(property->atoms()<=1000000) {
      env.statistics->phase=Statistics::NORMALIZATION;
      Normalisation norm;
      probUnits = norm.normalise(probUnits);
    }
  }

  env.statistics->phase=Statistics::UNKNOWN_PHASE;

  //now all the cpu usage will be in children, we'll just be waiting for them
  Timer::setTimeLimitEnforcement(false);

  //fork off the writer child process
  writerChildPid=Multiprocessing::instance()->fork();
  if(!writerChildPid) {
    runWriterChild();
    ASSERTION_VIOLATION; // the runWriterChild() function should never return
  }
  cout<<"writer pid "<<writerChildPid<<endl;
  cout.flush();

  //when the pipe will be closed, we want the process to terminate properly
  signal(SIGPIPE, &terminatingSignalHandler);

  //only the writer child is reading from the pipe (and it is now forked off)
  childOutputPipe.neverRead();

  env.setPipeOutput(&childOutputPipe); //direct output into the pipe
  UIHelper::cascMode=true;

  performStrategy();

  exitOnNoSuccess();
  ASSERTION_VIOLATION; //the exitOnNoSuccess() function should never return
}

/**
 * This function exits the problem master process if the problem
 * was not solved
 *
 * The unsuccessful problem master process does not have to
 * necessarily call this function to exit.
 */
void CLTBProblem::exitOnNoSuccess()
{
  CALL("CLTBProblem::exitOnNoSuccess");

  env.beginOutput();
  env.out()<<"% Proof not found in time "<<Timer::msToSecondsString(env.timer->elapsedMilliseconds())<<endl;
  if(env.remainingTime()/100>0) {
    env.out()<<"% SZS status GaveUp for "<<env.options->problemName()<<endl;
  }
  else {
    //From time to time we may also be terminating in the timeLimitReached()
    //function in Lib/Timer.cpp in case the time runs out. We, however, output
    //the same string there as well.
    env.out()<<"% SZS status Timeout for "<<env.options->problemName()<<endl;
  }
  env.endOutput();

  env.setPipeOutput(0);
  //This should make the writer child terminate.
  childOutputPipe.neverWrite();

  int resValue;
  pid_t lastChild=Multiprocessing::instance()->waitForChildTermination(resValue);
  ASS_EQ(lastChild, writerChildPid);
  ASS_EQ(resValue,0);


  cout<<"terminated solver pid "<<getpid()<<" (fail)"<<endl;
  cout.flush();

  System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
}

/**
 * Run schedule in @b sliceCodes. Terminate the process with 0 exit status
 * if proof was found, otherwise return false.
 */
bool CLTBProblem::runSchedule(Schedule& schedule,StrategySet& used,bool fallback)
{
  CALL("CLTBProblem::runSchedule");

  int parallelProcesses;
  unsigned coreNumber = System::getNumberOfCores();
  if(coreNumber<=1) {
    parallelProcesses = 1;
  }
  else if(coreNumber>=8) {
    parallelProcesses = coreNumber-2;
  }
  else {
    parallelProcesses = coreNumber-1;
  }

  int processesLeft=parallelProcesses;
  Schedule::Iterator it(schedule);
 
  while(it.hasNext()) {
    while(it.hasNext() && processesLeft) {
      ASS_G(processesLeft,0);

      int remainingTime = env.remainingTime()/100;
      if(remainingTime<=0) {
        return false;
      }
 
      string sliceCode = it.next();
      string chopped;
      int sliceTime = getSliceTime(sliceCode,chopped);
      if (fallback && used.contains(chopped)) {
	continue;
      }
      used.insert(chopped);
      if(sliceTime>remainingTime) {
	sliceTime=remainingTime;
      }

      pid_t childId=Multiprocessing::instance()->fork();
      ASS_NEQ(childId,-1);
      if(!childId) {
	//we're in a proving child
	runChild(sliceCode,sliceTime); //start proving
	ASSERTION_VIOLATION; //the runChild function should never return
      }
      Timer::syncClock();

      ASS(childIds.insert(childId));

      cout << "slice pid "<< childId << " slice: " << sliceCode << " time: " << sliceTime << endl << flush;
      processesLeft--;
    }

    if(processesLeft==0) {
      waitForChildAndExitWhenProofFound();
      processesLeft++;
    }
  }

  while(parallelProcesses!=processesLeft) {
    ASS_L(processesLeft, parallelProcesses);
    waitForChildAndExitWhenProofFound();
    processesLeft++;
    Timer::syncClock();
  }
  return false;
}

/**
 * Wait for termination of a child and terminate the process with a zero status
 * if a proof was found. If the child didn't find the proof, just return.
 */
void CLTBProblem::waitForChildAndExitWhenProofFound()
{
  CALL("CLTBProblem::waitForChildAndExitWhenProofFound");
  ASS(!childIds.isEmpty());

  int resValue;
  pid_t finishedChild=Multiprocessing::instance()->waitForChildTermination(resValue);
#if VDEBUG
  ALWAYS(childIds.remove(finishedChild));
#endif
  if(!resValue) {
    //we have found the proof. It has been already written down by the writter child,
    //so we can just terminate
    cout<<"terminated slice pid "<<finishedChild<<" (success)"<<endl;
    cout.flush();
    int writerResult;
    try {
    Multiprocessing::instance()->waitForParticularChildTermination(writerChildPid, writerResult);
    } catch(SystemFailException& ex) {
      //it may happen that the writer process has already exitted
      if(ex.err!=ECHILD) {
	throw;
      }
    }
    System::terminateImmediately(0);
  }
  cout<<"terminated slice pid "<<finishedChild<<" (fail)"<<endl;
  cout.flush();
}

ofstream* CLTBProblem::writerFileStream = 0;

/**
 * Read everything from the pipe and write it into the output file.
 * Terminate after all writing ends of the pipe are closed.
 *
 * This function is to be run in a forked-off process
 */
void CLTBProblem::runWriterChild()
{
  CALL("CLTBProblem::runWriterChild");

  System::registerForSIGHUPOnParentDeath();
  signal(SIGHUP, &terminatingSignalHandler);
  Timer::setTimeLimitEnforcement(false);

  //we're in the child that writes down the output of other children
  childOutputPipe.neverWrite();

  ofstream out(outFile.c_str());

  writerFileStream = &out;

  childOutputPipe.acquireRead();

  while(!childOutputPipe.in().eof()) {
    string line;
    getline(childOutputPipe.in(), line);
    if(line==problemFinishedString) {
      break;
    }
    out<<line<<endl<<flush;
  }
  out.close();
  writerFileStream = 0;

  childOutputPipe.releaseRead();

  System::terminateImmediately(0);
}

void CLTBProblem::terminatingSignalHandler(int sigNum)
{
  if(writerFileStream) {
    writerFileStream->close();
  }
  System::terminateImmediately(0);
}

void CLTBProblem::runChild(string slice, unsigned ds)
{
  CALL("CLTBProblem::runChild");

  Options opt=*env.options;
  opt.readFromTestId(slice);
  opt.setTimeLimitInDeciseconds(ds);
  int stl = opt.simulatedTimeLimit();
  if(stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  runChild(opt);
}

/**
 * Do the theorem proving in a forked-off process
 */
void CLTBProblem::runChild(Options& opt)
{
  CALL("CLTBProblem::runChild");

  System::registerForSIGHUPOnParentDeath();

  UIHelper::cascModeChild=true;

  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();
  Timer::setTimeLimitEnforcement(true);

  *env.options=opt;
  //we have already performed the normalization
  env.options->setNormalize(false);
  env.options->setForcedOptionValues();
  env.options->checkGlobalOptionConstraints();


//  if(env.options->sineSelection()!=Options::SS_OFF) {
//    //add selected axioms from the theory
//    parent->theorySelector.perform(probUnits);
//
//    env.options->setSineSelection(Options::SS_OFF);
//    env.options->forceIncompleteness();
//  }
//  else {
//    //if there wasn't any sine selection, just put in all theory axioms
//    probUnits=UnitList::concat(probUnits, parent->theoryAxioms);
//  }

  env.beginOutput();
  env.out()<<env.options->testId()<<" on "<<env.options->problemName()<<endl;
  env.endOutput();

  ProvingHelper::runVampire(probUnits,property);

  //set return value to zero if we were successful
  if(env.statistics->terminationReason==Statistics::REFUTATION) {
    resultValue=0;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  if(resultValue==0) {
    env.out()<<problemFinishedString<<endl;
  }
  env.endOutput();

  exit(resultValue);
}

/**
 * Return intended slice time in deciseconds and assign the slice string with
 * chopped time to @b chopped.
 */
unsigned CLTBProblem::getSliceTime(string sliceCode,string& chopped)
{
  CALL("CASCMode::getSliceTime");

  unsigned pos=sliceCode.find_last_of('_');
  string sliceTimeStr=sliceCode.substr(pos+1);
  chopped.assign(sliceCode.substr(0,pos));
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = (unsigned)(sliceTime * SLOWNESS) + 1;
  if (time < 10) {
    time++;
  }
  return time;
}

#endif //!COMPILER_MSVC
