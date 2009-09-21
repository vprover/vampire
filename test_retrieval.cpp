/**
 * @file test_retrieval.cpp
 */


#include <sys/time.h>
#include <sys/resource.h>

#include <fstream>
#include <csignal>
#include <utility>
#include <algorithm>

#include "Debug/Tracer.hpp"

#include "Lib/Array.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"

#include "Lib/Vector.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "Indexing/TermSharing.hpp"
#include "Indexing/SubstitutionTree.hpp"

#include "Shell/Options.hpp"
#include "Shell/CommandLine.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTP.hpp"
#include "Shell/TPTPParser.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Refutation.hpp"
#include "Shell/TheoryFinder.hpp"

#include "Resolution/ProofAttempt.hpp"

#include "Rule/CASC.hpp"
#include "Rule/Prolog.hpp"
#include "Rule/Index.hpp"
#include "Rule/ProofAttempt.hpp"

#include "Test/Output.hpp"

#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

using namespace std;
using namespace Shell;
using namespace Lib;
using namespace Resolution;
using namespace Indexing;

unsigned getCpuTime()
{
  struct timeval tim;
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  tim=ru.ru_utime;
  unsigned t=tim.tv_sec*1000 + tim.tv_usec / 1000;
  tim=ru.ru_stime;
  t+=tim.tv_sec*1000 + tim.tv_usec / 1000;
  return t;
}


template<typename T>
void randomize(Array<T>& arr, size_t cnt)
{
  while(cnt>1) {
    size_t swInd=Random::getInteger(cnt);
    cnt--;
    swap(arr[swInd], arr[cnt]);
  }
}


typedef pair<Literal*, Clause*> LCPair;
typedef pair<TermList*, Clause*> TCPair;

void doTest()
{
  CALL("doTest()");

  cout<<env.options->inputFile()<<":"<<endl;

  ifstream input(env.options->inputFile().c_str());
  TPTPLexer lexer(input);
  TPTPParser parser(lexer);
  UnitList* units = parser.units();

  Property property;
  property.scan(units);

  Preprocess prepro(property,*env.options);
  prepro.preprocess(units);

  cout<<"Unit count: "<<units->length()<<endl;


  Array<LCPair> literals;

  int index=0;
  UnitList::Iterator uit(units);

  //don't index the first clause, and store its first literal
  Clause* cls1=static_cast<Clause*>(uit.next());
  ASS(cls1->length()>=1);
  Literal* nonIndexedLit=(*cls1)[0];

  while(uit.hasNext()) {
    Unit* unit=uit.next();
    ASS(unit->isClause());
    Clause* cls=static_cast<Clause*>(unit);
    for(unsigned i=0;i<cls->length();i++) {
      literals[index++]=LCPair((*cls)[i], cls);
    }
  }
  int litCnt=index;

  Literal* indexedLit=literals[0].first;

  SubstitutionTree tree(2*env.signature->predicates());
  SubstitutionTree ttree(env.signature->functions()+1);

  Timer tmr;
  tmr.start();

  for(index=0;index<litCnt;index++) {
    tree.insert(literals[index].first, literals[index].second);
  }
  tmr.stop();
  cout<<litCnt<<" literals inserted in "<<tmr.elapsedMilliseconds()<<" ms."<<endl;

  cout<<tree.toString()<<endl;

  cout<<"Retrieving literals complementary unifiable with "<<Test::Output::toString(nonIndexedLit)<<":"<<endl;
  SLQueryResultIterator rit1=tree.getComplementaryUnifications(nonIndexedLit);
  while(rit1.hasNext()) {
    SLQueryResult res=rit1.next();
    cout<<Test::Output::toString(res.literal)<<" in "<<Test::Output::toString(res.clause)<<endl;
  }

  cout<<"Retrieving generalizations of "<<Test::Output::toString(nonIndexedLit)<<":"<<endl;
  SLQueryResultIterator rit2=tree.getGeneralizations(nonIndexedLit);
  while(rit2.hasNext()) {
    SLQueryResult res=rit2.next();
    cout<<Test::Output::toString(res.literal)<<" in "<<Test::Output::toString(res.clause)<<endl;
  }

  tmr.reset();
  tmr.start();
  for(index=0;index<litCnt;index++) {
    tree.remove(literals[index].first, literals[index].second);
  }
  tmr.stop();
  cout<<litCnt<<" literals removed in "<<tmr.elapsedMilliseconds()<<" ms."<<endl;

  cout<<endl;

#if CHECK_LEAKS
  delete env.signature;
  env.signature = 0;
  MemoryLeak leak;
  leak.release(units);
#endif
} // ruleMode

/**
 * Print an explanation about exception to cout either as a text or
 * as XML, depending on the environment.
 * @since 10/08/2005 Redmond
 */
void explainException (Exception& exception)
{
  exception.cry(cout);
} // explainException


/**
 * The main function.
 * @since 03/12/2003 many changes related to logging
 *        and exception handling.
 * @since 10/09/2004, Manchester changed to use knowledge bases
 */
int main(int argc, char* argv [])
{
  CALL ("main");

  // create random seed for the random number generation
  Lib::Random::resetSeed();

  try {
    // read the command line and interpret it
    Options options;
    Shell::CommandLine cl(argc,argv);
    cl.interpret(options);
    Allocator::setMemoryLimit(options.memoryLimit()*1000000);

    Timer timer;
    timer.start();
    env.timer = &timer;
    Indexing::TermSharing sharing;
    env.sharing = &sharing;
    env.options = &options;
    Shell::Statistics statistics;
    env.statistics = &statistics;
    env.signature = new Kernel::Signature;

    doTest();

  }
#if VDEBUG
  catch (Debug::AssertionViolationException& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
  }
#endif
  catch (Exception& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
  catch (std::bad_alloc& _) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    cout << "Insufficient system memory" << '\n';
  }
  //   delete env.allocator;
  return EXIT_SUCCESS;
} // main
