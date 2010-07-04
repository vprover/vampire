/**
 * @file CLTBMode.cpp
 * Implements class CLTBMode.
 */

#include <fstream>
#include <cstdlib>
#include <csignal>

//#include "Lib/Portability.hpp"

//#if !COMPILER_MSVC
//#include <unistd.h>
//#endif

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
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
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"
#include "Shell/UIHelper.hpp"

#include "CASCMode.hpp"

#include "SimpleLTBMode.hpp"

#define SLOWNESS 1.15

namespace Shell
{
namespace CASC
{

using namespace std;
using namespace Lib;
using namespace Lib::Sys;
using namespace Saturation;

/**
 * This function runs the batch master process and spawns the child master processes
 *
 * In this function we:
 * 1) read the batch file
 * 2) load the common axioms and put them into a SInE selector
 * 3) run a child master process for each problem (sequentially)
 */
void SimpleLTBMode::perform()
{
  CALL("SimpleLTBMode::perform");

  readInput();
  env.options->setTimeLimitInSeconds(overallTimeLimit);

  int solvedCnt=0;

  StringPairStack::BottomFirstIterator probs(problemFiles);
  while(probs.hasNext()) {
    StringPair res=probs.next();

    string probFile=res.first;
    string outFile=res.second;

    pid_t child=Multiprocessing::instance()->fork();
    if(!child) {
      SLTBProblem prob(this, probFile, outFile);
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

void SimpleLTBMode::readInput()
{
  CALL("SimpleLTBMode::readInput");

  if(env.options->inputFile()=="") {
    USER_ERROR("Input file must be specified for cltb mode");
  }

  string line, word;
  ifstream in(env.options->inputFile().c_str());
  if(in.fail()) {
    USER_ERROR("Cannot open input file: "+env.options->inputFile());
  }

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
  if(word!="limit.time.problem.wc") {
    USER_ERROR("\"limit.time.problem.wc\" expected, \""+word+"\" found.");
  }
  in>>problemTimeLimit;

  in>>word;
  if(word!="limit.time.overall.wc") {
    USER_ERROR("\"limit.time.overall.wc\" expected, \""+word+"\" found.");
  }
  in>>overallTimeLimit;

  std::getline(in, line);
  while(!in.eof() && line=="") { std::getline(in, line); }
  if(line!="% SZS end BatchConfiguration") {
    USER_ERROR("\"% SZS end BatchConfiguration\" expected, \""+line+"\" found.");
  }
  std::getline(in, line);
  if(line!="% SZS start BatchIncludes") {
    USER_ERROR("\"% SZS start BatchIncludes\" expected, \""+line+"\" found.");
  }

  for(std::getline(in, line); line[0]!='%' && !in.eof(); std::getline(in, line)) {
    //we just skip includes
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
// SLTBProblem
//////////////////////////////////////////

SLTBProblem::SLTBProblem(SimpleLTBMode* parent, string problemFile, string outFile)
: parent(parent), problemFile(problemFile), outFile(outFile)
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
void SLTBProblem::performStrategy()
{
  CALL("SLTBProblem::performStrategy");

  Property::Category cat = property.category();
  unsigned prop = property.props();
  unsigned atoms = property.atoms();

  cout << "Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  const char* backupSlices[] = {
    "dis+10_32_nwc=2.0:sac=on:spl=backtracking_10000",
    "dis+4_8_10000",
    0
  };
  const char* empty[] = {0};
  const char** quickSlices = empty;
  const char** slowSlices = empty; // set to empty for categories having no slow slices

  switch (cat) {
  case Property::NEQ: {
    if (prop == 3) {
      const char* quick[] = {
	"lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_3",
	"dis-1010_10_bd=off:bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sio=off:sp=reverse_arity_5",
	"lrs-4_1_bd=off:bs=off:bms=on:ecs=on:gsp=input_only:nicw=on:ssec=off:stl=60:sos=on:sio=off:spl=off_2",
	"dis-1010_3:1_bs=off:drc=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_49",
	"dis-1010_3:1_bd=off:ep=R:flr=on:gsp=input_only:lcm=predicate:nwc=4.0:sswn=on:sswsr=on:sio=off_5",
	"lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_2",
	"lrs+10_128_bd=off:bs=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.2:stl=60:sp=reverse_arity_48",
	"dis+1010_6_bd=off:nwc=10.0:ssec=off:sac=on:sp=occurrence_23",
	"lrs+1_4:1_bd=off:bs=off:cond=on:fde=none:lcm=predicate:stl=60:sos=on_565",
	"lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_413",
	"lrs+1002_2:1_bd=off:bs=unit_only:bsr=on:cond=on:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:stl=60:sac=on:sio=off:sp=occurrence_201",
	"lrs+10_1_bd=off:bs=off:cond=on:flr=on:fde=none:gsp=input_only:stl=60:updr=off_434",
	0
      };
      quickSlices = quick;
      break;
    }
    if (prop < 3) {
      const char* quick[] = {
	"dis+1_2:1_drc=off:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sio=off:spl=backtracking:sp=reverse_arity:updr=off_5",
	"dis+3_4_bd=off:bs=off:cond=fast:ep=on:lcm=reverse:nwc=10.0:sswsr=on:sgo=on:sp=occurrence_6",
	"dis+11_6_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:swb=on:sp=occurrence:updr=off_5",
	"lrs+10_128_bd=off:bs=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.2:stl=60:sp=reverse_arity_39",
	"dis+1011_50_bs=unit_only:gsp=input_only:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:updr=off_24",
	"lrs+2_6_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.3:ptb=off:ssec=off:stl=90:sagn=off:sio=off:spo=on:sp=occurrence_11",
	"lrs-4_1_bd=off:bs=off:bms=on:ecs=on:gsp=input_only:nicw=on:ssec=off:stl=60:sos=on:sio=off:spl=off_1",
	"dis+10_5_bs=off:cond=on:flr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=occurrence_47",
	"lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_114",
	"lrs+11_5_bs=off:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=4:ptb=off:ssec=off:stl=60:sagn=off:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence_116",
	"dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_376",
	"lrs-1002_64_bd=off:bs=unit_only:bsr=unit_only:cond=fast:flr=on:fde=none:nwc=1.2:nicw=on:sswn=on:sswsr=on:stl=60:sfv=off:sp=occurrence_317",
	"lrs-10_3:2_bs=off:bms=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=5.0:ssec=off:stl=60:sio=off_436",
	0
      };
      quickSlices = quick;
      break;
    }
    if (prop == 131079) {
      const char* quick[] = {
	"dis+2_2:3_bsr=unit_only:cond=on:drc=off:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sgo=on:spo=on:swb=on:sfv=off:sp=occurrence:updr=off_21",
	"dis+11_28_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:ep=on:fsr=off:fde=none:lcm=reverse:nwc=10:sswn=on:sswsr=on:sac=on:spo=on:sfv=off:sp=reverse_arity:updr=off_3",
	"lrs+1004_1_bd=off:bs=off:cond=fast:ep=on:gsp=input_only:lcm=predicate:nwc=3.0:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spl=backtracking:updr=off_40",
	"dis+11_10_bd=off:bs=off:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=4:nicw=on:ssec=off:sac=on:sp=occurrence_111",
	"dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_7",
	"dis+1011_50_bs=unit_only:gsp=input_only:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:updr=off_44",
	"dis-1004_6_bd=off:bs=off:cond=fast:drc=off:flr=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_37",
	"dis+11_5:1_cond=fast:ep=on:gsp=input_only:nwc=10:sswn=on:sswsr=on_6",
	"dis+1011_5_bd=off:bs=unit_only:cond=on:flr=on:fde=none:nwc=1.5:nicw=on:ptb=off:ssec=off:sgo=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity_149",
	"lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_48",
	"dis+10_24_bd=off:drc=off:ep=R:nwc=1.5:nicw=on:ptb=off:ssec=off:sagn=off:sio=off:spo=on:spl=backtracking:sp=reverse_arity_16",
	"dis+11_6_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:swb=on:sp=occurrence:updr=off_16",
	"lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_118",
	"dis+11_12_bs=unit_only:cond=on:flr=on:fde=none:lcm=reverse:nwc=1.5:sswn=on:sswsr=on:sgo=on:sfv=off:sp=reverse_arity_395",
	"lrs+10_1_bd=off:bs=off:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=3.0:stl=60:sp=reverse_arity_146",
	"dis+10_50_bs=off:ecs=on:ep=on:fde=none:gsp=input_only:nwc=4.0:nicw=on:ssec=off:sac=on:sgo=on:spo=on_484",
	"dis+1_50_cond=fast:lcm=predicate:nwc=3.0_597",
	"dis-3_32_bs=unit_only:bsr=unit_only:cond=fast:ep=on:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:sswsr=on:sac=on:sfv=off_44",
	0
      };
      quickSlices = quick;
      break;
    }
    const char* quick[] = {
      "dis+2_5:1_cond=on:flr=on:gsp=input_only:lcm=predicate:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence_1",
      "dis+1002_10_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_47",
      "dis+1011_5_bd=off:bs=unit_only:cond=on:flr=on:fde=none:nwc=1.5:nicw=on:ptb=off:ssec=off:sgo=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity_1",
      "dis-1010_5:1_bs=off:cond=fast:ep=R:gsp=input_only:nwc=1.1:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:swb=on:sp=occurrence_8",
      "lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_3",
      "dis+10_5_bs=off:cond=on:flr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=occurrence_3",
      "dis+2_3:1_bd=off:bs=off:ep=on:flr=on:gsp=input_only:lcm=reverse:nwc=3.0:ptb=off:ssec=off:sos=on:sgo=on:spl=backtracking:sp=reverse_arity_1",
      "dis+1010_6_bd=off:nwc=10.0:ssec=off:sac=on:sp=occurrence_6",
      "dis+1_50_cond=fast:lcm=predicate:nwc=3.0_21",
      "dis+4_10_bd=off:bs=off:cond=fast:fde=none:nwc=10.0:ptb=off:ssec=off:sgo=on:spl=backtracking:sp=reverse_arity_148",
      "lrs+10_5_bs=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=3.0:stl=60:sos=on:sio=off:spl=off_1",
      "lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_52",
      "lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_113",
      "dis-1010_3:1_bd=off:ep=R:flr=on:gsp=input_only:lcm=predicate:nwc=4.0:sswn=on:sswsr=on:sio=off_31",
      "lrs+10_1_bd=off:bs=off:cond=on:flr=on:fde=none:gsp=input_only:stl=60:updr=off_142",
      "lrs+1_4:1_bd=off:bs=off:cond=on:fde=none:lcm=predicate:stl=60:sos=on_4",
      "dis-1010_3:1_bs=off:drc=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_11",
      "dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_53",
      0
    };
    quickSlices = quick;
    break;
  }

  case Property::HEQ: {
    const char* quick[] = {
      "lrs-1_32_bd=off:bs=off:bsr=on:cond=on:ecs=on:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ssec=off:stl=60:sac=on:sio=off:spo=on:sp=occurrence_2",
      "dis+2_10_bd=off:bs=unit_only:bsr=unit_only:ep=RS:fsr=off:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_2",
      "lrs+2_1_bms=on:cond=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:stl=60:sos=on:sac=on:sgo=on:spo=on:sp=reverse_arity_1",
      "dis+1_4_bd=off:bs=off:cond=on:flr=on:gsp=input_only:lcm=predicate:nwc=5.0:ptb=off:ssec=off:spo=on:spl=backtracking_82",
      "dis+2_40_bd=off:bs=off:cond=fast:fsr=off:gsp=input_only:nwc=4.0:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spl=backtracking:sp=reverse_arity_410",
      "dis+11_12_bd=off:bs=off:bms=on:cond=fast:drc=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=5:sswsr=on:sac=on:sio=off:sfv=off:sp=reverse_arity:updr=off_26",
      "lrs+11_128_bd=off:bs=off:bsr=on:bms=on:cond=on:drc=off:flr=on:fde=none:nwc=1.3:nicw=on:sswn=on:stl=60:sio=off:sfv=off:sp=reverse_arity_33",
      "lrs+1010_5_bd=off:bs=off:bms=on:fde=none:gsp=input_only:nwc=2.5:nicw=on:sswsr=on:stl=60:sgo=on:sio=off:sp=reverse_arity:updr=off_8",
      "lrs-1004_2_bs=off:drc=off:ep=on:flr=on:fsr=off:gsp=input_only:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sswn=on:stl=90:sac=on:spo=on:sfv=off:sp=occurrence:updr=off_204",
      "lrs-1002_5_bs=off:bms=on:drc=off:ep=on:flr=on:fsr=off:fde=none:nwc=1:nicw=on:ssec=off:stl=60:sac=on:sfv=off_85",
      "lrs-1_3:2_bs=off:bms=on:drc=off:ep=on:fsr=off:nwc=1.7:sswn=on:sswsr=on:stl=60:sp=occurrence_154",
      "lrs+1011_2_bs=unit_only:bms=on:cond=on:drc=off:flr=on:fsr=off:lcm=predicate:nwc=4:nicw=on:sswsr=on:stl=60:sagn=off:sio=off:sfv=off:sp=occurrence:updr=off_506",
      "dis+2_5_bd=off:bs=off:cond=fast:gsp=input_only:nwc=4.0:nicw=on:sgo=on:sio=off_489",
      0
    };
    quickSlices = quick;
    break;
  }

  case Property::PEQ: {
    if (prop == 0) {
      const char* quick[] = {
	"lrs-4_2_bs=off:bms=on:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.2:nicw=on:stl=60:sac=on:sio=off:spo=on:sfv=off_283",
	"lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_40",
	"lrs+1_5_bd=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:flr=on:fde=none:nwc=10:stl=60:sagn=off:sac=on:sio=off:sp=reverse_arity_134",
	"dis-4_40_bs=unit_only:bsr=on:drc=off:ep=on:nwc=10:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=reverse_arity_297",
	"dis-1_10_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:fsr=off:nwc=1.2:sswn=on:sagn=off:spo=on:sfv=off_409",
	"dis+1003_8_bs=off:flr=on:fsr=off:gsp=input_only:nwc=1.2:ssec=off:sac=on:sgo=on:sio=off:sp=occurrence_153",
	"lrs-11_7_bs=off:bms=on:drc=off:ep=on:nwc=1.5:sswn=on:sswsr=on:stl=60:sgo=on:sp=reverse_arity_578",
	"lrs+4_4_bd=off:bsr=unit_only:bms=on:cond=on:drc=off:ecs=on:flr=on:fsr=off:fde=none:gsp=input_only:nwc=5:nicw=on:ssec=off:stl=60:sac=on:sio=off:spo=on:sfv=off_227",
	"lrs-1010_8_bs=off:cond=fast:ep=on:fsr=off:gsp=input_only:nwc=1.1:nicw=on:sswn=on:sswsr=on:stl=60:sac=on:updr=off_286",
	"dis-11_32_bd=off:bs=unit_only:cond=on:drc=off:fsr=off:fde=none:nwc=1.5:ptb=off:ssec=off:sac=on:sgo=on:spo=on:swb=on:sfv=off:sp=occurrence_701",
	"lrs-4_5:1_bs=off:drc=off:flr=on:fsr=off:fde=none:nwc=1:ssec=off:stl=60:sac=on:sio=off:spo=on:sp=occurrence_538",
	0
      };
      quickSlices = quick;
      break;
    }
    if (prop == 1) {
      const char* quick[] = {
	"lrs+1010_8_cond=on:flr=on:nwc=1:sswn=on:sswsr=on:stl=60:sac=on:sgo=on:spo=on:updr=off_48",
	"lrs+1_5_bd=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:flr=on:fde=none:nwc=10:stl=60:sagn=off:sac=on:sio=off:sp=reverse_arity_13",
	"lrs+1003_5_flr=on:fde=none:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:updr=off_107",
	"lrs-4_5:1_bs=off:drc=off:flr=on:fsr=off:fde=none:nwc=1:ssec=off:stl=60:sac=on:sio=off:spo=on:sp=occurrence_55",
	"dis+1003_28_bsr=on:drc=off:flr=on:fsr=off:fde=none:gsp=input_only:nwc=1.3:sos=on:sfv=off_260",
	"dis+1004_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:flr=on:fsr=off:gsp=input_only:nwc=1.5:sswsr=on:sac=on:sio=off:spo=on:sfv=off_296",
	"lrs+3_3:2_bd=off:bs=off:drc=off:flr=on:gsp=input_only:nwc=10:sswn=on:stl=60:sagn=off:sfv=off:sp=occurrence_379",
	"lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_389",
	0
      };
      quickSlices = quick;
      break;
    }
    const char* quick[] = {
      "lrs+1003_8_bs=off:bms=on:cond=on:drc=off:ep=on:flr=on:nwc=1:ssec=off:stl=60:sagn=off:sac=on:sgo=on:sio=off:spo=on_25",
      "dis+1004_128_cond=on:ep=on:flr=on:gsp=input_only:nwc=3.0:updr=off_115",
      "lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_1",
      "lrs+11_5:4_bd=off:bs=unit_only:bms=on:drc=off:flr=on:fsr=off:nwc=2.5:nicw=on:ssec=off:stl=90:sac=on:sgo=on:sio=off:spo=on_70",
      "lrs+10_5_bsr=on:drc=off:ep=on:gsp=input_only:nwc=1.2:stl=60:sos=on:updr=off_424",
      "lrs-10_12_bd=off:bs=off:bms=on:cond=on:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:sswn=on:sswsr=on:stl=60:sfv=off_332",
      "lrs-4_5:1_bs=off:drc=off:flr=on:fsr=off:fde=none:nwc=1:ssec=off:stl=60:sac=on:sio=off:spo=on:sp=occurrence_13",
      0
    };
    quickSlices = quick;
    break;
  }

  case Property::HNE: {
    if (prop == 8192) {
      const char* quick[] = {
	"lrs+4_6_bs=unit_only:bsr=unit_only:bms=on:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ssec=off:stl=60:sio=off:sp=occurrence_14",
	"dis+1010_7_cond=fast:flr=on:fsr=off:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:spo=on:swb=on:updr=off_22",
	"dis+11_1_bs=unit_only:bms=on:cond=fast:ecs=on:fsr=off:lcm=predicate:nwc=4:nicw=on:ssec=off:sgo=on:sio=off:sp=reverse_arity:updr=off_55",
	"dis+2_2:3_flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=5.0:sio=off:spl=off:updr=off_709",
	"dis+11_128_bs=unit_only:bsr=unit_only:bms=on:cond=fast:flr=on:fsr=off:lcm=reverse:nwc=1.5:nicw=on:sio=off:sp=occurrence_420",
	"dis+1_40_bs=off:ecs=on:fsr=off:lcm=predicate:nwc=5:ssec=off:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_560",
	"lrs+2_14_bs=off:flr=on:gsp=input_only:nwc=3.0:nicw=on:stl=60:sgo=on:spo=on:sp=reverse_arity_524",
	0
      };
      quickSlices = quick;
      break;
    }
    const char* quick[] = {
      "dis+11_128_bs=unit_only:bsr=unit_only:bms=on:cond=fast:flr=on:fsr=off:lcm=reverse:nwc=1.5:nicw=on:sio=off:sp=occurrence_4",
      "dis+2_32_bs=off:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity:updr=off_9",
      "dis-1004_40_cond=fast:ecs=on:flr=on:fsr=off:gsp=input_only:nicw=on:ssec=off:sac=on:sgo=on:spo=on_38",
      "lrs+1002_6_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=3.0:ptb=off:ssec=off:stl=60:sio=off:spl=off:sp=reverse_arity:updr=off_4",
      "dis+1_40_bs=off:ecs=on:fsr=off:lcm=predicate:nwc=5:ssec=off:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_228",
      "lrs+10_3_bs=off:ep=on:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking_112",
      "lrs+2_4_bs=off:gsp=input_only:nwc=4.0:nicw=on:sswn=on:stl=60:sac=on:sio=off:sp=reverse_arity:updr=off_190",
      "lrs+1_8:1_bs=off:cond=fast:ecs=on:nwc=1.2:ssec=off:stl=90:sos=on:sac=on:sgo=on:sio=off:spo=on:sp=occurrence_729",
      "lrs+1002_5:4_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:nicw=on:ptb=off:ssec=off:stl=90:sac=on:sgo=on:sio=off:spl=backtracking_17",
      0
    };
    quickSlices = quick;
    break;
  }

  case Property::NNE: {
    if (prop == 65536) {
      const char* quick[] = {
	"dis+10_6_ecs=on:lcm=reverse:nwc=5.0:ssec=off:sio=off:spl=off:sp=reverse_arity:updr=off_48",
	"dis+4_7_bs=off:cond=fast:ecs=on:gsp=input_only:nwc=2.0:ssec=off:sgo=on:spo=on:updr=off_72",
	"dis+1010_20_lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_7",
	"dis+1002_40_flr=on:gsp=input_only:lcm=reverse:nwc=1.5:nicw=on:ssec=off:sac=on:sgo=on_40",
	"dis+1011_6_bs=unit_only:bsr=unit_only:flr=on:lcm=reverse:nwc=1.5:nicw=on:sswsr=on:sac=on:sio=off:spo=on:sp=occurrence_123",
	"lrs+10_10_cond=fast:lcm=reverse:nwc=2.0:sswsr=on:stl=90:sp=reverse_arity:updr=off_132",
	"dis-4_7_bs=off:ecs=on:gsp=input_only:lcm=reverse:nwc=2.0:ssec=off:sio=off:spl=off_141",
	"lrs+1011_32_bs=off:bsr=unit_only:flr=on:lcm=reverse:nwc=1.3:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking:sp=occurrence:updr=off_231",
	"dis-2_14_bs=off:cond=fast:flr=on:lcm=predicate:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking:updr=off_530",
	"dis-1002_12_bs=unit_only:flr=on:gsp=input_only:lcm=reverse:nwc=4:ptb=off:ssec=off:sagn=off:sac=on:sgo=on:spl=backtracking:sp=occurrence_631",
	0
      };
      quickSlices = quick;
      break;
    }
    const char* quick[] = {
      "dis+1011_40_bs=unit_only:bsr=unit_only:cond=fast:flr=on:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sio=off:spl=backtracking:sp=reverse_arity:updr=off_63",
      "lrs+10_5:4_bs=off:ep=on:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking_36",
      "lrs+1003_28_bs=off:cond=on:lcm=reverse:nwc=3:ptb=off:ssec=off:stl=60:sos=on:sac=on:spl=backtracking:sp=reverse_arity_309",
      "dis+2_3_bs=off:gsp=input_only:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence:updr=off_97",
      "dis-2_14_bs=off:cond=fast:flr=on:lcm=predicate:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking:updr=off_88",
      "dis+1002_40_bd=off:cond=on:lcm=predicate:nwc=1.7:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_106",
      "dis+10_12_gsp=input_only:nicw=on:sswn=on:sac=on:sgo=on:sio=off:spo=on:sp=occurrence_121",
      "dis+3_10_bs=off:flr=on:gsp=input_only:lcm=reverse:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_250",
      "lrs+10_10_cond=fast:lcm=reverse:nwc=2.0:sswsr=on:stl=90:sp=reverse_arity:updr=off_1",
      0
    };
    quickSlices = quick;
    break;
  }

  case Property::FEQ: {
    if (prop == 2) {
      const char* quick[] = {
	"lrs+1004_20_bs=off:drc=off:flr=on:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:updr=off_49",
	"lrs-1004_20_bs=off:bms=on:cond=fast:drc=off:flr=on:nwc=1.1:stl=60:sio=off:spl=off:sfv=off:updr=off_574",
	"lrs-11_10_bd=off:bs=off:cond=fast:drc=off:fsr=off:fde=none:lcm=predicate:nwc=2:ptb=off:ssec=off:stl=60:sagn=off:spl=backtracking:sfv=off:sp=occurrence_83",
	"lrs+1004_8_bd=off:bs=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:stl=60:sgo=on:sio=off:spl=backtracking:sp=reverse_arity_186",
	"lrs-4_64_bd=off:bs=unit_only:drc=off:ep=on:flr=on:fsr=off:gsp=input_only:lcm=reverse:nwc=1.2:stl=60:sac=on:sgo=on:sfv=off:sp=occurrence_577",
	"lrs+1010_50_bs=off:drc=off:flr=on:lcm=predicate:nwc=1.2:stl=60:sgo=on:sfv=off_551",
	"dis+11_40_bs=off:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:sac=on:sgo=on:spl=backtracking_413",
	"lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_299",
	0
      };
      quickSlices = quick;
      break;
    }
    if (prop == 131087) {
      if (atoms > 200000) {
	const char* quick[] = {
	  "dis-2_64_bd=off:bs=unit_only:bsr=on:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sd=1:ss=included:sos=on:sio=off:sfv=off_28",
	  "lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_54",
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_40",
	  "dis-1004_40_bd=off:bms=on:drc=off:fde=none:lcm=reverse:nwc=1.1:nicw=on:sd=1:ss=axioms:st=5.0:sos=on:sgo=on:sp=reverse_arity_24",
	  "lrs-4_1_bsr=on:bms=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:stl=60:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_28",
	  "lrs+1002_2_bd=off:bs=off:bsr=unit_only:bms=on:cond=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswn=on:stl=60:sd=1:ss=axioms:st=5.0:sos=on:sac=on:sgo=on:sio=off:sfv=off:updr=off_51",
	"dis-2_8_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=R:flr=on:fde=none:gsp=input_only:nwc=1.7:nicw=on:sswn=on:sswsr=on:sd=2:ss=included:st=1.2:sos=on:sio=off:spl=off:sfv=off_62",
	  "lrs-10_5:4_bd=off:bs=off:bsr=on:cond=fast:drc=off:flr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=30:sd=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_29",
	  "dis+2_5:4_bd=off:bs=unit_only:bsr=unit_only:ep=on:nwc=1.2:ssec=off:sd=1:ss=included:st=3.0:sos=on:spo=on:sp=occurrence_458",
	  "dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_46",
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_82",
	  "lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_500",
	  "lrs-2_128_bd=off:bs=off:drc=off:ep=R:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:sswn=on:stl=30:sd=7:ss=axioms:st=1.2:sos=on_255",
	  "dis-1003_3:1_bd=off:bs=unit_only:bsr=unit_only:cond=on:ep=RST:gsp=input_only:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=1:ss=included:st=1.2:sos=on:sagn=off:sac=on:swb=on:sfv=off:sp=occurrence_443",
	  "lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_359",
	  "lrs+1002_10_bd=off:bs=off:bsr=unit_only:ecs=on:gsp=input_only:lcm=reverse:nwc=1.2:nicw=on:ssec=off:stl=30:sd=1:ss=included:st=1.2:sos=on:sio=off:spl=off:sfv=off_45",
	  0
	};
	quickSlices = quick;
	break;
      }
      if (atoms > 100000) {
	const char* quick[] = {
	  "lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_64",
	  "dis-1010_5:1_bd=off:bsr=on:drc=off:ep=on:fde=none:nwc=1.1:ptb=off:ssec=off:sd=1:ss=included:sagn=off:sac=on:sgo=on:sio=off:sfv=off:sp=occurrence_45",
	  "lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_14",
	  "lrs-10_5:4_bd=off:bs=off:bsr=on:cond=fast:drc=off:flr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=30:sd=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_10",
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_12",
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_19",
	  "dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_46",
	  "dis-3_2:3_bd=off:bs=off:cond=fast:ep=RST:fsr=off:gsp=input_only:nwc=2:ssec=off:sd=2:ss=included:st=1.5:sos=on:sgo=on:sio=off:updr=off_18",
	  "lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_197",
	  "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_512",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_350",
	  "dis+2_5:4_bd=off:bs=unit_only:bsr=unit_only:ep=on:nwc=1.2:ssec=off:sd=1:ss=included:st=3.0:sos=on:spo=on:sp=occurrence_181",
	  "dis-1003_3:1_bd=off:bs=unit_only:bsr=unit_only:cond=on:ep=RST:gsp=input_only:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=1:ss=included:st=1.2:sos=on:sagn=off:sac=on:swb=on:sfv=off:sp=occurrence_366",
	  "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_484",
	  "lrs+10_1_bs=off:cond=fast:ep=on:lcm=predicate:stl=60:sos=on:updr=off_565",
	  0
	};
	quickSlices = quick;
	break;
      }
      if (atoms > 20000) {
	const char* quick[] = {
	  "dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_40",
	  "dis-1004_40_bd=off:bms=on:drc=off:fde=none:lcm=reverse:nwc=1.1:nicw=on:sd=1:ss=axioms:st=5.0:sos=on:sgo=on:sp=reverse_arity_10",
	  "lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_45",
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_8",
	  "lrs-4_1_bsr=on:bms=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:stl=60:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_16",
	  "lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_48",
	  "dis-2_64_bd=off:bs=unit_only:bsr=on:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sd=1:ss=included:sos=on:sio=off:sfv=off_7",
	  "dis-2_8_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=R:flr=on:fde=none:gsp=input_only:nwc=1.7:nicw=on:sswn=on:sswsr=on:sd=2:ss=included:st=1.2:sos=on:sio=off:spl=off:sfv=off_16",
	  "lrs-10_5:4_bd=off:bs=off:bsr=on:cond=fast:drc=off:flr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=30:sd=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_9",
	  "dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_6",
	  "lrs-2_128_bd=off:bs=off:drc=off:ep=R:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:sswn=on:stl=30:sd=7:ss=axioms:st=1.2:sos=on_4",
	  "dis-1010_5:1_bd=off:bsr=on:drc=off:ep=on:fde=none:nwc=1.1:ptb=off:ssec=off:sd=1:ss=included:sagn=off:sac=on:sgo=on:sio=off:sfv=off:sp=occurrence_35",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_119",
	  "dis+2_5:4_bd=off:bs=unit_only:bsr=unit_only:ep=on:nwc=1.2:ssec=off:sd=1:ss=included:st=3.0:sos=on:spo=on:sp=occurrence_184",
	  "lrs+11_14_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_96",
	  "lrs+10_1_bs=off:cond=fast:ep=on:lcm=predicate:stl=60:sos=on:updr=off_354",
	  "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_397",
	  "dis-1003_3:1_bd=off:bs=unit_only:bsr=unit_only:cond=on:ep=RST:gsp=input_only:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=1:ss=included:st=1.2:sos=on:sagn=off:sac=on:swb=on:sfv=off:sp=occurrence_419",
	  0
	};
	quickSlices = quick;
	break;
      }
      if (atoms > 2000) {
	const char* quick[] = {
	  "dis+11_1_bs=unit_only:ep=R:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:sos=on:sagn=off:sgo=on:sio=off:spl=backtracking:sp=occurrence:updr=off_21",
	  "lrs+1002_2_bd=off:bs=off:bsr=unit_only:bms=on:cond=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswn=on:stl=60:sd=1:ss=axioms:st=5.0:sos=on:sac=on:sgo=on:sio=off:sfv=off:updr=off_3",
	  "lrs+1_8:1_bd=off:bs=off:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:stl=60:sos=on:sagn=off:sgo=on:sio=off:sp=occurrence_5",
	  "lrs-4_1_bsr=on:bms=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:stl=60:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_6",
	  "dis-2_64_bd=off:bs=unit_only:bsr=on:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sd=1:ss=included:sos=on:sio=off:sfv=off_3",
	  "dis-3_2:3_bd=off:bs=off:cond=fast:ep=RST:fsr=off:gsp=input_only:nwc=2:ssec=off:sd=2:ss=included:st=1.5:sos=on:sgo=on:sio=off:updr=off_3",
	  "lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_6",
	  "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_53",
	  "lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_49",
	  "dis+2_5:4_bd=off:bs=unit_only:bsr=unit_only:ep=on:nwc=1.2:ssec=off:sd=1:ss=included:st=3.0:sos=on:spo=on:sp=occurrence_189",
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_9",
	  "dis-1004_40_bd=off:bms=on:drc=off:fde=none:lcm=reverse:nwc=1.1:nicw=on:sd=1:ss=axioms:st=5.0:sos=on:sgo=on:sp=reverse_arity_6",
	  "lrs+11_4:1_bs=off:ep=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:stl=60:sio=off:spl=off:sp=occurrence:updr=off_34",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_361",
	  "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_163",
	  "dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_435",
	  "dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_221",
	  "lrs+10_1_bs=off:cond=fast:ep=on:lcm=predicate:stl=60:sos=on:updr=off_185",
	  "lrs+10_2:1_bs=off:bms=on:cond=fast:drc=off:flr=on:fde=none:lcm=predicate:nwc=1:ssec=off:stl=60:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_207",
	  "lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_219",
	  "dis+10_1_ep=R:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_139",
	  0
	};
	quickSlices = quick;
	break;
      }
      // prop == 131087 && atoms <= 2000
      const char* quick[] = {
	"dis+1011_8:1_bs=off:drc=off:ep=RS:fde=none:nwc=1:ptb=off:ssec=off:sio=off:swb=on:sp=occurrence_7",
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_11",
	"lrs-1010_4:1_bd=off:bsr=on:drc=off:ep=on:flr=on:fde=none:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:sd=1:ss=included:st=1.2:sos=on:sagn=off:sio=off:swb=on:sfv=off:sp=reverse_arity_2",
	"lrs-1_4:1_bd=off:bs=off:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=5:ptb=off:ssec=off:stl=60:sio=off:sfv=off:sp=occurrence_13",
	"dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_14",
	"lrs+1011_3_bs=unit_only:bsr=unit_only:cond=on:drc=off:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=60:sgo=on:sio=off:spl=backtracking:sfv=off_59",
	"dis+1003_2_bsr=unit_only:bms=on:cond=fast:flr=on:fde=none:gsp=input_only:nwc=1.5:ssec=off:sac=on:sfv=off:sp=reverse_arity:updr=off_31",
	"dis-1010_5:1_bd=off:bsr=on:drc=off:ep=on:fde=none:nwc=1.1:ptb=off:ssec=off:sd=1:ss=included:sagn=off:sac=on:sgo=on:sio=off:sfv=off:sp=occurrence_6",
	"dis+1004_4:1_bs=off:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=1:nicw=on:sswn=on:sac=on:sio=off:sfv=off:sp=occurrence:updr=off_33",
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_38",
	"lrs+11_5:1_bd=off:bs=off:cond=fast:ep=RST:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_116",
	"lrs+1011_8_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=RST:flr=on:fsr=off:gsp=input_only:lcm=reverse:nwc=1.5:ptb=off:ssec=off:stl=60:sagn=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity_50",
	"dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_131",
	"dis+1004_2:3_bd=off:ep=RST:nwc=10:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_87",
	"lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_498",
	"dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_492",
	"dis+10_1_ep=R:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_492",
	"lrs+10_3_bd=off:bs=off:cond=on:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:stl=60:sos=on_565",
	0
      };
      quickSlices = quick;
      break;
    }
    // ./tune.pl a 'category="FEQ" AND property NOT IN (2,131087)' 240

    if (prop == 0) {
      const char* quick[] = {
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_24",
	"lrs+11_40_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:lcm=predicate:nwc=1:ptb=off:ssec=off:stl=60:sac=on:spl=backtracking:sfv=off:updr=off_21",
	"lrs+10_7_bd=off:bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sagn=off:sgo=on:spo=on:spl=backtracking:sp=reverse_arity:updr=off_169",
	"dis+1003_2_bsr=unit_only:bms=on:cond=fast:flr=on:fde=none:gsp=input_only:nwc=1.5:ssec=off:sac=on:sfv=off:sp=reverse_arity:updr=off_99",
	"lrs-1_5_bd=off:drc=off:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:stl=60:sagn=off:spl=backtracking:sp=occurrence:updr=off_2",
	"lrs+1011_1_bs=off:bsr=unit_only:drc=off:flr=on:fsr=off:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:stl=60:spl=backtracking_150",
	"dis+3_64_bd=off:bs=unit_only:bsr=on:cond=on:ep=on:fde=none:gsp=input_only:nwc=10:nicw=on:ptb=off:ssec=off:sagn=off:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_108",
	"dis+10_1_bs=off:flr=on:gsp=input_only:lcm=predicate:sos=on:sp=reverse_arity:updr=off_297",
	"dis-2_4_bs=unit_only:bsr=on:cond=fast:drc=off:flr=on:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sswsr=on:sagn=off:sio=off:spl=backtracking_1",
	"lrs-1004_32_fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking:sp=occurrence_278",
	"dis-1002_32_bd=off:bs=off:bms=on:cond=on:drc=off:ep=on:flr=on:lcm=reverse:nwc=1.2:nicw=on:sswn=on:sswsr=on:spo=on:sfv=off_220",
	"dis+1003_5_drc=off:ep=on:lcm=reverse:nwc=1:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=reverse_arity:updr=off_478",
	"lrs+4_20_cond=fast:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sac=on:sgo=on:updr=off_459",
	"lrs-1003_20_bsr=unit_only:bms=on:cond=fast:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=2:stl=60:sd=4:ss=axioms:st=1.5:sos=on:sio=off:spl=off_486",
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_250",
	"lrs-11_10_bd=off:bs=off:cond=fast:drc=off:fsr=off:fde=none:lcm=predicate:nwc=2:ptb=off:ssec=off:stl=60:sagn=off:spl=backtracking:sfv=off:sp=occurrence_2",
	"dis+1_6_bs=unit_only:bsr=on:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=1.3:sswn=on:sswsr=on:sd=1:ss=included:st=1.5:spo=on_299",
	0
      };
      quickSlices = quick;
      break;
    }
    if (prop == 1) {
      const char* quick[] = {
	"dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_1",
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_9",
	"lrs+11_14_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_23",
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_70",
	"lrs-1003_12_bs=unit_only:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:lcm=predicate:nwc=10:nicw=on:ssec=off:stl=60:sgo=on:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_2",
	"lrs+1010_50_bs=off:drc=off:flr=on:lcm=predicate:nwc=1.2:stl=60:sgo=on:sfv=off_16",
	"dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_30",
	"lrs+1_2:1_bs=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_175",
	"lrs+11_40_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:lcm=predicate:nwc=1:ptb=off:ssec=off:stl=60:sac=on:spl=backtracking:sfv=off:updr=off_230",
	"lrs-1010_10_bd=off:bs=unit_only:cond=on:flr=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_207",
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_380",
	"lrs-1010_7_bs=off:bsr=on:bms=on:cond=on:drc=off:ecs=on:ep=on:flr=on:fsr=off:fde=none:lcm=predicate:nwc=1.3:nicw=on:ssec=off:stl=60:sac=on:sgo=on:sio=off_8",
	"dis+3_5:4_bd=off:bs=off:drc=off:ep=RST:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sswn=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_195",
	"lrs+1002_10_bd=off:bs=off:bsr=unit_only:ecs=on:gsp=input_only:lcm=reverse:nwc=1.2:nicw=on:ssec=off:stl=30:sd=1:ss=included:st=1.2:sos=on:sio=off:spl=off:sfv=off_199",
	0
      };
      quickSlices = quick;
      break;
    }
    if ((prop & 131072) == 0) {
      const char* quick[] = {
	"dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_1",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_54",
	"dis+2_5:4_bd=off:bs=unit_only:bsr=unit_only:ep=on:nwc=1.2:ssec=off:sd=1:ss=included:st=3.0:sos=on:spo=on:sp=occurrence_3",
	"lrs-1003_12_bs=unit_only:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:lcm=predicate:nwc=10:nicw=on:ssec=off:stl=60:sgo=on:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_18",
	"lrs+1011_5_bs=off:bsr=unit_only:drc=off:ep=RST:flr=on:lcm=reverse:nwc=4:nicw=on:sswsr=on:stl=60:sagn=off:sac=on:sgo=on:sio=off:sfv=off:sp=occurrence_1",
	"lrs+2_28_bs=off:bms=on:cond=on:drc=off:fsr=off:fde=none:lcm=predicate:nwc=1.7:stl=60:sagn=off:sgo=on:spo=on:sfv=off_10",
	"dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_21",
	"dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_150",
	"dis+2_50_fde=none:lcm=predicate:ss=included:st=3.0:sos=on:updr=off_6",
	"dis+3_5:4_bd=off:bs=off:drc=off:ep=RST:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sswn=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_9",
	"lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_218",
	"lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_137",
	"lrs+10_2:1_bs=off:bms=on:cond=fast:drc=off:flr=on:fde=none:lcm=predicate:nwc=1:ssec=off:stl=60:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_170",
	"dis+3_24_bsr=on:drc=off:ep=on:fde=none:gsp=input_only:nwc=4:ptb=off:ssec=off:sgo=on:sio=off:swb=on_284",
	"dis+1004_20_bd=off:bs=off:gsp=input_only:lcm=reverse:nwc=2.0:nicw=on:ptb=off:ssec=off:sgo=on:sio=off:spl=backtracking:sp=occurrence:updr=off_303",
	0
      };
      quickSlices = quick;
      break;
    }
    if (prop == 131073) {
      if (atoms > 400) {
	const char* quick[] = {
	  "dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_3",
	  "dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_28",
	  "lrs-1010_10_bd=off:bs=unit_only:cond=on:flr=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_14",
	  "lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_4",
	  "lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_6",
	  "dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_76",
	  "lrs+1011_3_bs=unit_only:bsr=unit_only:cond=on:drc=off:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=60:sgo=on:sio=off:spl=backtracking:sfv=off_8",
	  "dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_2",
	  "lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_20",
	  "lrs+11_5:1_bd=off:bs=off:cond=fast:ep=RST:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_17",
	  "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_155",
	  "lrs+1_2:1_bs=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_52",
	  "dis+10_1_ep=R:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_291",
	  "lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_171",
	  "lrs-1010_4_bd=off:bs=off:cond=fast:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=30:spl=backtracking_293",
	  "dis-3_2:3_bd=off:bs=off:cond=fast:ep=RST:fsr=off:gsp=input_only:nwc=2:ssec=off:sd=2:ss=included:st=1.5:sos=on:sgo=on:sio=off:updr=off_5",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_247",
	  "dis+11_40_bd=off:bs=unit_only:bsr=on:drc=off:ep=on:fde=none:lcm=predicate:nwc=1.2:sswn=on:sswsr=on:sagn=off:sgo=on:sfv=off:sp=reverse_arity_43",
	  "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_60",
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_71",
	  "dis-1002_1_cond=fast:lcm=predicate:nwc=2.5_149",
	  0
	};
	quickSlices = quick;
	break;
      }
      const char* quick[] = {
	"dis+1010_8_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:fde=none:nwc=1.5:nicw=on:sagn=off:sac=on:sgo=on:sio=off:sfv=off:updr=off_17",
	"dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_104",
	"lrs+1011_3_bs=unit_only:bsr=unit_only:cond=on:drc=off:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=60:sgo=on:sio=off:spl=backtracking:sfv=off_7",
	"dis+2_1_bd=off:bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_1",
	"dis+1011_8_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:swb=on:sp=reverse_arity:updr=off_29",
	"dis-1002_32_bd=off:bs=off:bms=on:cond=on:drc=off:ep=on:flr=on:lcm=reverse:nwc=1.2:nicw=on:sswn=on:sswsr=on:spo=on:sfv=off_11",
	"dis-1010_5:4_bms=on:cond=fast:ep=on:flr=on:fde=none:nwc=5:nicw=on:sd=2:ss=axioms:sos=on:sac=on:spo=on:sfv=off_8",
	"dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_3",
	"lrs+2_1_drc=off:ecs=on:ep=on:gsp=input_only:lcm=predicate:nwc=1:ssec=off:stl=60:sd=2:ss=axioms:st=1.2:sos=on:sfv=off:sp=occurrence_6",
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_100",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_272",
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_278",
	"lrs+11_14_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_51",
	"dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_107",
	"dis-1010_4_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_554",
	"lrs+1002_10_bd=off:bs=off:bsr=unit_only:ecs=on:gsp=input_only:lcm=reverse:nwc=1.2:nicw=on:ssec=off:stl=30:sd=1:ss=included:st=1.2:sos=on:sio=off:spl=off:sfv=off_114",
	"dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_237",
	"dis-1002_4_bs=off:fsr=off:fde=none:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:swb=on_7",
	"dis-2_64_bd=off:bs=unit_only:bsr=on:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sd=1:ss=included:sos=on:sio=off:sfv=off_16",
	"dis-1010_5:1_bd=off:bsr=on:drc=off:ep=on:fde=none:nwc=1.1:ptb=off:ssec=off:sd=1:ss=included:sagn=off:sac=on:sgo=on:sio=off:sfv=off:sp=occurrence_31",
	0
      };
      quickSlices = quick;
      break;
    }
    if (prop & 2) {
      const char* quick[] = {
	"dis-1010_4_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_6",
	"lrs+4_1_cond=on:ep=RS:flr=on:fde=none:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:stl=60:ss=axioms:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_1",
	"lrs+1011_3_bs=unit_only:bsr=unit_only:cond=on:drc=off:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=60:sgo=on:sio=off:spl=backtracking:sfv=off_11",
	"lrs+11_14_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_72",
	"dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_10",
	"lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_59",
	"dis+2_1_bd=off:bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_2",
	"lrs+3_12_bs=off:cond=on:flr=on:fde=none:gsp=input_only:sswsr=on:stl=60:sp=occurrence:updr=off_7",
	"lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spl=backtracking_4",
	"lrs-4_1_bsr=on:bms=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:stl=60:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_5",
	"dis+11_40_bd=off:bs=unit_only:bsr=on:drc=off:ep=on:fde=none:lcm=predicate:nwc=1.2:sswn=on:sswsr=on:sagn=off:sgo=on:sfv=off:sp=reverse_arity_1",
	"dis+11_40_bs=off:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:sac=on:sgo=on:spl=backtracking_36",
	"lrs-1010_10_bd=off:bs=unit_only:cond=on:flr=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_47",
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_385",
	"dis+1003_3:2_bd=off:bsr=on:fsr=off:fde=none:gsp=input_only:nwc=2.5:nicw=on:ssec=off:sac=on:sgo=on:sfv=off:sp=occurrence_142",
	"dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_529",
	"dis+1010_8_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:fde=none:nwc=1.5:nicw=on:sagn=off:sac=on:sgo=on:sio=off:sfv=off:updr=off_376",
	"lrs+10_1_bs=off:cond=fast:ep=on:lcm=predicate:stl=60:sos=on:updr=off_383",
	0
      };
      quickSlices = quick;
      break;
    }
    const char* quick[] = {
      "lrs-1010_10_bd=off:bs=unit_only:cond=on:flr=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_3",
      "lrs+4_14_bd=off:bs=off:cond=on:ep=R:flr=on:lcm=predicate:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking_6",
      "dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_90",
      "dis-1010_4_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_45",
      "lrs+10_1_bs=off:cond=fast:ep=on:lcm=predicate:stl=60:sos=on:updr=off_4",
      "lrs+2_5:4_bms=on:cond=on:ep=on:flr=on:fde=none:lcm=reverse:nwc=1.5:nicw=on:sswn=on:stl=60:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_1",
      "lrs+1002_2_bd=off:bs=off:bsr=unit_only:bms=on:cond=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sswn=on:stl=60:sd=1:ss=axioms:st=5.0:sos=on:sac=on:sgo=on:sio=off:sfv=off:updr=off_1",
      "dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_23",
      "dis+1004_4_bd=off:bs=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_15",
      "dis+11_40_bs=off:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=10:ptb=off:ssec=off:sac=on:sgo=on:spl=backtracking_10",
      "dis+1_6_bs=unit_only:bsr=on:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=1.3:sswn=on:sswsr=on:sd=1:ss=included:st=1.5:spo=on_12",
      "dis+10_1_ep=R:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_2",
      "dis-2_20_flr=on:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_126",
      "lrs+1011_5:1_bd=off:cond=fast:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_1",
      "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_29",
      "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_139",
      "lrs+1_2:1_bs=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_199",
      "lrs-10_5:4_bd=off:bs=off:bsr=on:cond=fast:drc=off:flr=on:gsp=input_only:nwc=1:ptb=off:ssec=off:stl=30:sd=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_85",
      "dis+1011_5_bs=off:cond=fast:drc=off:ep=on:lcm=predicate:nwc=1.5:nicw=on:sswn=on:sswsr=on:sac=on:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_90",
      "dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_465",
      "dis+11_40_bd=off:bs=unit_only:bsr=on:drc=off:ep=on:fde=none:lcm=predicate:nwc=1.2:sswn=on:sswsr=on:sagn=off:sgo=on:sfv=off:sp=reverse_arity_302",
      "lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spl=backtracking_398",
      "dis+2_1_bd=off:bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_473",
      0
    };
    quickSlices = quick;
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
  case Property::EPR: {
    const char* quick[] = {
      "lrs+1_40_bs=unit_only:gsp=input_only:lcm=reverse:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spl=backtracking:sfv=off:updr=off_8",
      "dis+10_7_bd=off:bs=off:gsp=input_only:nwc=5.0:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:sp=occurrence:updr=off_345",
      "lrs+3_2_bd=off:bs=off:bms=on:cond=on:ecs=on:ep=R:flr=on:fsr=off:lcm=predicate:nwc=2.0:ssec=off:stl=90:sac=on_51",
      "dis+10_128_bd=off:bs=off:ep=RST:flr=on:lcm=predicate:nwc=1.2:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_635",
      "lrs+1_8_bd=off:cond=fast:ep=RST:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_426",
      "lrs+1003_16_bd=off:bs=off:cond=fast:ep=R:flr=on:fsr=off:gsp=input_only:stl=90:updr=off_283",
      "dis+3_3:2_bs=off:ecs=on:ep=R:flr=on:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ssec=off:sac=on:sgo=on:spo=on_65",
      0
    };
    quickSlices = quick;
    break;
  }
  case Property::UEQ: {
    if (prop == 0) {
      const char* quick[] = {
	"lrs+10_14_bs=off:fde=none:stl=60:sp=occurrence_33",
	"lrs+10_40_bsr=on:drc=off:fde=none:gsp=input_only:nwc=5:stl=90:sp=reverse_arity_787",
	"lrs+10_5:4_bs=off:flr=on:nwc=5.0:stl=60:sp=occurrence_96",
	"lrs+10_5:1_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.1:stl=60_334",
	"lrs+10_1_bs=off:bsr=on:drc=off:fsr=off:fde=none:nwc=1.7:stl=90:sp=occurrence_326",
	"lrs+10_1_bs=off:drc=off:nwc=1.3:stl=90_390",
	"dis+10_64_bs=unit_only:drc=off:fsr=off:nwc=2:sp=reverse_arity_733",
	0
      };
      quickSlices = quick;
      break;
    }
    // prop != 0
    const char* quick[] = {
      "lrs+10_7_bs=off:bsr=on:drc=off:fde=none:nwc=4:stl=90:sp=reverse_arity_20",
      "lrs+10_64_bs=unit_only:drc=off:fde=none:gsp=input_only:nwc=3:stl=60:sp=occurrence_37",
      "lrs+10_20_bs=off:bsr=on:drc=off:nwc=1.3:stl=90:sp=reverse_arity_239",
      "dis+10_128_bs=unit_only:drc=off:fsr=off:fde=none:gsp=input_only:nwc=10_143",
      "lrs+10_2:3_bs=unit_only:drc=off:fsr=off:nwc=4:stl=60:sp=reverse_arity_161",
      "lrs+10_10_bd=off:bs=off:bsr=unit_only:drc=off:fde=none:gsp=input_only:nwc=3:stl=60:sp=occurrence_51",
      "lrs+10_8:1_bs=off:fsr=off:gsp=input_only:nwc=1.3:stl=120_111",
      "dis+10_7_bd=off:bsr=unit_only:drc=off:nwc=1.5_168",
      "lrs+10_128_bd=off:bs=unit_only:drc=off:gsp=input_only:nwc=1.3:stl=60:sp=occurrence_357",
      "lrs+10_5:4_fsr=off:fde=none:nwc=2.5:stl=90:sp=occurrence_505",
      "lrs+10_2:3_bsr=on:drc=off:nwc=1.2:stl=60:sp=reverse_arity_188",
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


void SLTBProblem::perform()
{
  CALL("SLTBProblem::perform");

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
    TPTPLexer lexer(inp);
    TPTPParser parser(lexer);

    probUnits = parser.units();
    UIHelper::setConjecturePresence(parser.haveConjecture());
  }

  {
    TimeCounter tc(TC_PREPROCESSING);
    env.statistics->phase=Statistics::PROPERTY_SCANNING;

    property.scan(probUnits);

    env.statistics->phase=Statistics::NORMALIZATION;

    Normalisation norm;
    probUnits = norm.normalise(probUnits);
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
void SLTBProblem::exitOnNoSuccess()
{
  CALL("SLTBProblem::exitOnNoSuccess");

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
bool SLTBProblem::runSchedule(const char** sliceCodes)
{
  CALL("SLTBProblem::runSchedule");

  int parallelProcesses=max(1u,System::getNumberOfCores()-1);
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
void SLTBProblem::waitForChildAndExitWhenProofFound()
{
  CALL("SLTBProblem::waitForChildAndExitWhenProofFound");
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
    System::terminateImmediately(0);
  }
  cout<<"terminated slice pid "<<finishedChild<<" (fail)"<<endl;
  cout.flush();
}

/**
 * Read everything from the pipe and write it into the output file.
 * Terminate after all writing ends of the pipe are closed.
 *
 * This function is to be run in a forked-off process
 */
void SLTBProblem::runWriterChild()
{
  CALL("SLTBProblem::runWriterChild");

  System::registerForSIGHUPOnParentDeath();
  signal(SIGHUP, &terminatingSignalHandler);
  Timer::setTimeLimitEnforcement(false);

  //we're in the child that writes down the output of other children
  childOutputPipe.neverWrite();

  ofstream out(outFile.c_str());

  childOutputPipe.acquireRead();

  while(!childOutputPipe.in().eof()) {
    string line;
    getline(childOutputPipe.in(), line);
    out<<line<<endl;
  }
  out.close();

  childOutputPipe.releaseRead();

  System::terminateImmediately(0);
}

void SLTBProblem::terminatingSignalHandler(int sigNum)
{
  System::terminateImmediately(0);
}

void SLTBProblem::runChild(string slice, unsigned ds)
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
void SLTBProblem::runChild(Options& opt)
{
  CALL("SLTBProblem::runChild");

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

  env.beginOutput();
  env.out()<<env.options->testId()<<" on "<<env.options->problemName()<<endl;
  env.endOutput();

  ProvingHelper::runVampire(probUnits, &property);

  //set return value to zero if we were successful
  if(env.statistics->terminationReason==Statistics::REFUTATION) {
    resultValue=0;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  exit(resultValue);
}

/**
 * Return intended slice time in deciseconds
 */
unsigned SLTBProblem::getSliceTime(string sliceCode)
{
  CALL("SLTBProblem::getSliceTime");

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
