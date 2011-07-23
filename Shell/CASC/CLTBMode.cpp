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

namespace Shell
{
namespace CASC
{

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
    pid_t finishedChild=Multiprocessing::instance()->waitForChildTermination(resValue);
    ASS_EQ(finishedChild, child);

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
: parent(parent), problemFile(problemFile), outFile(outFile), property(parent->property)
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

  Property::Category cat = property->category();
  unsigned atoms = property->atoms();

  cout << "Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  const char* backupSlices[] = {
    "dis+11_128_nwc=5.0:sac=on:ss=included:st=3.0:spl=backtracking_10000",
    "dis+10_32_nwc=2.0:sac=on:spl=backtracking_10000",
    "dis+4_8_10000",
    0
  };
  const char* empty[] = {0};
  const char** quickSlices = empty;
  const char** slowSlices = empty; // set to empty for categories having no slow slices

  switch (cat) {
  case Property::FEQ: {
    if (atoms > 1000000) {
      const char* quick[] = {
	"dis+1_14_bsr=unit_only:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sd=10:ss=included:st=1.5:sagn=off:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_754",
	"dis+1002_8:1_bs=unit_only:bsr=on:cond=on:ep=RS:fde=none:nwc=2:ptb=off:ssec=off:ss=included:sio=off:spo=on:swb=on:sp=reverse_arity_711",
	"lrs+4_10_bd=off:bs=off:drc=off:ep=on:flr=on:fsr=off:lcm=reverse:nwc=3:ptb=off:ssec=off:stl=120:sd=7:ss=included:st=2.0:sos=on:sio=off:spo=on:spl=backtracking:updr=off_707",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 600000) {
      const char* quick[] = {
	"lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_120",
	"dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_117",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 450000) {
      const char* quick[] = {
	"lrs+1002_2_bd=off:bs=off:bsr=unit_only:bms=on:cond=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswn=on:stl=60:sd=1:ss=axioms:st=5.0:sos=on:sac=on:sgo=on:sio=off:sfv=off:updr=off_53",
	"lrs+1002_10_bd=off:bs=off:bsr=unit_only:ecs=on:gsp=input_only:lcm=reverse:nwc=1.2:nicw=on:ssec=off:stl=30:sd=1:ss=included:st=1.2:sos=on:sio=off:spl=off:sfv=off_45",
	"dis-1010_1_bd=off:bs=unit_only:bsr=on:bms=on:cond=fast:ep=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sd=1:ss=axioms:sac=on:sgo=on:sio=off:sp=occurrence:updr=off_42",
	"dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_46",
	"lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_50",
	"dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_82",
	"dis-1010_5:1_bd=off:bsr=on:drc=off:ep=on:fde=none:nwc=1.1:ptb=off:ssec=off:sd=1:ss=included:sagn=off:sac=on:sgo=on:sio=off:sfv=off:sp=occurrence_125",
	"lrs-2_128_bd=off:bs=off:drc=off:ep=R:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:sswn=on:stl=30:sd=7:ss=axioms:st=1.2:sos=on_255",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 350000) {
      const char* quick[] = {
	"lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_45",
	"lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_40",
	"lrs-10_5:4_bd=off:bs=off:bsr=on:cond=fast:drc=off:flr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=30:sd=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_29",
	"dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_139",
	"lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_359",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 250000) {
      const char* quick[] = {
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_71",
	"lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_48",
	"lrs-2_128_bd=off:bs=off:drc=off:ep=R:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:sswn=on:stl=30:sd=7:ss=axioms:st=1.2:sos=on_22",
	"lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_23",
	"dis-1_14_bd=off:bsr=unit_only:bms=on:ep=RST:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswsr=on:sd=1:ss=included:sos=on:spo=on:sp=reverse_arity_34",
	"dis-4_8_bs=unit_only:drc=off:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:sio=off:swb=on_46",
	"dis+2_1_bd=off:bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_200",
	"lrs+1_4:1_bs=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sd=1:ss=included:st=3.0:sos=on:sio=off:swb=on:sp=reverse_arity_340",
	"dis-1003_3:1_bd=off:bs=unit_only:bsr=unit_only:cond=on:ep=RST:gsp=input_only:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=1:ss=included:st=1.2:sos=on:sagn=off:sac=on:swb=on:sfv=off:sp=occurrence_443",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 150000) {
      const char* quick[] = {
	"lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_24",
	"dis+2_3_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:nicw=on:sswn=on:sswsr=on:sd=1:ss=included:sac=on:sio=off:spo=on:sp=occurrence_78",
	"dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_46",
	"lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_24",
	"dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_17",
	"dis-4_8_bs=unit_only:drc=off:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:sio=off:swb=on_27",
	"dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_518",
	"dis+2_5:4_bd=off:bs=unit_only:bsr=unit_only:ep=on:nwc=1.2:ssec=off:sd=1:ss=included:st=3.0:sos=on:spo=on:sp=occurrence_153",
	"dis+1_6_bs=unit_only:bsr=on:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=1.3:sswn=on:sswsr=on:sd=1:ss=included:st=1.5:spo=on_395",
	"dis-1002_7_bs=unit_only:lcm=reverse:nwc=1.1:ptb=off:ssec=off:sd=2:ss=axioms:st=1.2:sos=on:sgo=on:sio=off:spl=backtracking:sp=reverse_arity:updr=off_22",
	"dis-1010_5:1_bd=off:bsr=on:drc=off:ep=on:fde=none:nwc=1.1:ptb=off:ssec=off:sd=1:ss=included:sagn=off:sac=on:sgo=on:sio=off:sfv=off:sp=occurrence_30",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 120000) {
      const char* quick[] = {
	"dis-1002_7_bs=unit_only:lcm=reverse:nwc=1.1:ptb=off:ssec=off:sd=2:ss=axioms:st=1.2:sos=on:sgo=on:sio=off:spl=backtracking:sp=reverse_arity:updr=off_11",
	"dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_10",
	"lrs-10_5:4_bd=off:bs=off:bsr=on:cond=fast:drc=off:flr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=30:sd=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_10",
	"dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_19",
	"lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_11",
	"lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_14",
	"dis-3_2:3_bd=off:bs=off:cond=fast:ep=RST:fsr=off:gsp=input_only:nwc=2:ssec=off:sd=2:ss=included:st=1.5:sos=on:sgo=on:sio=off:updr=off_12",
	"dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_65",
	"lrs+11_2:3_bs=off:cond=fast:ecs=on:ep=on:fsr=off:fde=none:lcm=predicate:nwc=5:nicw=on:ssec=off:stl=30:sd=1:ss=axioms:sio=off:spo=on:sp=reverse_arity:updr=off_13",
	"dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_53",
	"lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_64",
	"lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_197",
	"lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_439",
	"dis-1_14_bd=off:bsr=unit_only:bms=on:ep=RST:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswsr=on:sd=1:ss=included:sos=on:spo=on:sp=reverse_arity_8",
	"lrs+1002_2_bd=off:bs=off:bsr=unit_only:bms=on:cond=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswn=on:stl=60:sd=1:ss=axioms:st=5.0:sos=on:sac=on:sgo=on:sio=off:sfv=off:updr=off_10",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 90000) {
      const char* quick[] = {
	"dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_76",
	"lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_8",
	"dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_58",
	"dis-1003_3:1_bd=off:bs=unit_only:bsr=unit_only:cond=on:ep=RST:gsp=input_only:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=1:ss=included:st=1.2:sos=on:sagn=off:sac=on:swb=on:sfv=off:sp=occurrence_366",
	"lrs+1_4:1_bs=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sd=1:ss=included:st=3.0:sos=on:sio=off:swb=on:sp=reverse_arity_248",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 60000) {
      const char* quick[] = {
	"lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_6",
	"lrs+1_2:1_bs=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_13",
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_9",
	"lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_8",
	"dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_6",
	"dis-1010_1_bd=off:bs=unit_only:bsr=on:bms=on:cond=fast:ep=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sd=1:ss=axioms:sac=on:sgo=on:sio=off:sp=occurrence:updr=off_6",
	"dis-4_8_bs=unit_only:drc=off:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:sio=off:swb=on_16",
	"lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_45",
	"dis-1002_7_bs=unit_only:lcm=reverse:nwc=1.1:ptb=off:ssec=off:sd=2:ss=axioms:st=1.2:sos=on:sgo=on:sio=off:spl=backtracking:sp=reverse_arity:updr=off_10",
	"lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_9",
	"lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_48",
	"dis+2_5:4_bd=off:bs=unit_only:bsr=unit_only:ep=on:nwc=1.2:ssec=off:sd=1:ss=included:st=3.0:sos=on:spo=on:sp=occurrence_184",
	"dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_530",
	"dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_119",
	"lrs+10_1_bs=off:cond=fast:ep=on:lcm=predicate:stl=60:sos=on:updr=off_354",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 15000) {
      const char* quick[] = {
	"lrs-2_128_bd=off:bs=off:drc=off:ep=R:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:sswn=on:stl=30:sd=7:ss=axioms:st=1.2:sos=on_4",
	"dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_16",
	"dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_45",
	"lrs-10_5:4_bd=off:bs=off:bsr=on:cond=fast:drc=off:flr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=30:sd=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_3",
	"lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_49",
	"dis-1_14_bd=off:bsr=unit_only:bms=on:ep=RST:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswsr=on:sd=1:ss=included:sos=on:spo=on:sp=reverse_arity_4",
	"lrs-1003_6_cond=on:ep=on:flr=on:fsr=off:fde=none:lcm=predicate:nwc=10:ptb=off:ssec=off:stl=60:sd=1:ss=axioms:st=1.5:sio=off:swb=on:sp=reverse_arity_5",
	"dis-1003_3:1_bd=off:bs=unit_only:bsr=unit_only:cond=on:ep=RST:gsp=input_only:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=1:ss=included:st=1.2:sos=on:sagn=off:sac=on:swb=on:sfv=off:sp=occurrence_10",
	"lrs+1002_2_bd=off:bs=off:bsr=unit_only:bms=on:cond=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswn=on:stl=60:sd=1:ss=axioms:st=5.0:sos=on:sac=on:sgo=on:sio=off:sfv=off:updr=off_6",
	"dis+1004_2:1_bd=off:bs=off:bsr=unit_only:ep=on:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=1:sswn=on:sd=1:ss=included:st=3.0:sos=on:sagn=off:sfv=off:sp=reverse_arity_9",
	"dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_9",
	"dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_40",
	"lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sd=2:ss=included:sio=off:spl=backtracking_6",
	"lrs+1_4:1_bs=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sd=1:ss=included:st=3.0:sos=on:sio=off:swb=on:sp=reverse_arity_30",
	"dis-1004_40_bd=off:bms=on:drc=off:fde=none:lcm=reverse:nwc=1.1:nicw=on:sd=1:ss=axioms:st=5.0:sos=on:sgo=on:sp=reverse_arity_6",
	"dis-4_8_bs=unit_only:drc=off:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:sio=off:swb=on_19",
	"dis-3_2:3_bd=off:bs=off:cond=fast:ep=RST:fsr=off:gsp=input_only:nwc=2:ssec=off:sd=2:ss=included:st=1.5:sos=on:sgo=on:sio=off:updr=off_3",
	"lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_10",
	"lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_13",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_28",
	"dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_361",
	"lrs+11_14_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_96",
	"dis+10_1_ep=R:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_237",
	"dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_381",
	"dis-1002_1_cond=fast:lcm=predicate:nwc=2.5_149",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 10000) {
      const char* quick[] = {
	"dis+1011_3_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ssec=off:sos=on:spo=on:sp=reverse_arity_2",
      "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_2",
	"lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:stl=60:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_3",
	"lrs+3_28_bd=off:bs=unit_only:bms=on:drc=off:ep=on:flr=on:fsr=off:fde=none:nwc=1.3:ssec=off:stl=120:sd=3:ss=included:st=2.0:sagn=off:sac=on:sgo=on:sio=off:spo=on:sp=occurrence_2",
	"lrs-10_5:4_bd=off:bs=off:bsr=on:cond=fast:drc=off:flr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=30:sd=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_3",
	"dis+1003_8_bms=on:ecs=on:lcm=predicate:nwc=3.0:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:updr=off_40",
	"lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_6",
	"dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_253",
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_73",
	"dis+11_1_bs=unit_only:ep=R:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:sos=on:sagn=off:sgo=on:sio=off:spl=backtracking:sp=occurrence:updr=off_21",
	"dis+2_3_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:nicw=on:sswn=on:sswsr=on:sd=1:ss=included:sac=on:sio=off:spo=on:sp=occurrence_193",
	"dis+2_5:4_bd=off:bs=unit_only:bsr=unit_only:ep=on:nwc=1.2:ssec=off:sd=1:ss=included:st=3.0:sos=on:spo=on:sp=occurrence_189",
	0
      };
      quickSlices = quick;
    }
    else {
      const char* quick[] = {
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_4",
	"lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_1",
	"dis+1003_8_bms=on:ecs=on:lcm=predicate:nwc=3.0:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:updr=off_4",
	"lrs+1_2:1_bs=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_52",
	"dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_16",
	"dis-1010_4_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_45",
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_48",
	"dis+1002_128_bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sgo=on:spl=backtracking:updr=off_1",
	"dis+11_40_bs=off:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:sac=on:sgo=on:spl=backtracking_36",
	"lrs+11_14_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_72",
	"dis+1011_5_bs=off:cond=fast:drc=off:ep=on:lcm=predicate:nwc=1.5:nicw=on:sswn=on:sswsr=on:sac=on:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_90",
	"dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_107",
	"lrs+10_1_bs=off:cond=fast:ep=on:lcm=predicate:stl=60:sos=on:updr=off_383",
	"dis+1004_20_bd=off:bs=off:gsp=input_only:lcm=reverse:nwc=2.0:nicw=on:ptb=off:ssec=off:sgo=on:sio=off:spl=backtracking:sp=occurrence:updr=off_4",
	"lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_5",
	"dis+1011_8:1_bs=off:drc=off:ep=RS:fde=none:nwc=1:ptb=off:ssec=off:sio=off:swb=on:sp=occurrence_26",
	0
      };
      quickSlices = quick;
    }
    break;
  }
  case Property::FNE: {
    const char* quick[] = {
      "dis+10_10_bs=off:gsp=input_only:lcm=reverse:nwc=10.0:nicw=on:sswn=on:sgo=on_62",
      "lrs+11_3:2_bs=unit_only:bsr=unit_only:cond=on:fsr=off:lcm=predicate:nwc=1.3:ptb=off:ssec=off:stl=60:sac=on:spl=backtracking_26",
      "dis+10_24_bsr=unit_only:cond=fast:nwc=10:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_4",
      "dis+4_10_bs=off:ep=on:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_16",
      "dis-4_128_nwc=1.2:ptb=off:ssec=off:sac=on:sgo=on:swb=on:sp=reverse_arity_7",
      "dis+1011_3_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ssec=off:sos=on:spo=on:sp=reverse_arity_22",
      "dis+1002_32_fsr=off:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sos=on:sagn=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_6",
      "dis+1011_128_bsr=on:bms=on:cond=on:fsr=off:lcm=reverse:nwc=4:nicw=on:sswn=on:sswsr=on:sac=on:sio=off:sp=occurrence:updr=off_57",
      "dis+1002_24_bs=off:cond=on:ecs=on:lcm=reverse:ssec=off:spo=on:sp=reverse_arity:updr=off_217",
      "dis+1002_128_bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sgo=on:spl=backtracking:updr=off_32",
      "dis+1004_5_bs=off:flr=on:lcm=predicate:nwc=5.0:ptb=off:ssec=off:sgo=on:swb=on:sp=occurrence_148",
      "dis+2_28_bs=off:lcm=reverse:nwc=1:nicw=on:sswn=on:sswsr=on:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_564",
      "lrs+1002_2:3_bs=off:bsr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=60:sagn=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_441",
      "dis+10_128_bs=off:cond=on:fsr=off:gsp=input_only:lcm=reverse:nwc=3.0:ptb=off:ssec=off:sos=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_316",
      0
    };
    quickSlices = quick;
    break;
  }
  }

  int remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return;
  }
  if (runSchedule(quickSlices)) {
    return;
  }
  remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return;
  }
  if (runSchedule(slowSlices)) {
    return;
  }
  if(remainingTime<=0) {
    return;
  }
  runSchedule(backupSlices);
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

    property = Property::scan(probUnits);
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
bool CLTBProblem::runSchedule(const char** sliceCodes)
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

  const char** nextSlice=sliceCodes;

  while(*nextSlice) {
    while(*nextSlice && processesLeft) {
      ASS_G(processesLeft,0);

      int remainingTime = env.remainingTime()/100;
      if(remainingTime<=0) {
        return false;
      }
      int sliceTime = getSliceTime(*nextSlice);
      if(sliceTime>remainingTime) {
	sliceTime=remainingTime;
      }


      pid_t childId=Multiprocessing::instance()->fork();
      ASS_NEQ(childId,-1);
      if(!childId) {
        //we're in a proving child
        runChild(*nextSlice, sliceTime); //start proving

        ASSERTION_VIOLATION; //the runChild function should never return
      }
      Timer::syncClock();

#if VDEBUG
      ALWAYS(childIds.insert(childId));
#endif

      cout<<"slice pid "<<childId<<" slice: "<<(*nextSlice)<<" time: "<<sliceTime<<endl;
      cout.flush();


      nextSlice++;
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
 * Return intended slice time in deciseconds
 */
unsigned CLTBProblem::getSliceTime(string sliceCode)
{
  CALL("CLTBProblem::getSliceTime");

  string sliceTimeStr=sliceCode.substr(sliceCode.find_last_of('_')+1);
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr, sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = (unsigned)(sliceTime * SLOWNESS) + 1;
  if (time < 10) {
    time++;
  }
  return time;
}


}
}


#endif //!COMPILER_MSVC
