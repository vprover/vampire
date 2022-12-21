#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/LiteralIndex.hpp"
#include <chrono>

#include "SATSubsumption/ForwardBenchmarkWrapper.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

static std::chrono::high_resolution_clock::duration totalDuration = chrono::duration<int64_t, std::nano>::zero();
static ofstream outputFile;
static ofstream problemFile;

ForwardBenchmarkWrapper::ForwardBenchmarkWrapper(bool subsumptionResolution) : _forwardBenchmark(subsumptionResolution), _forwardOracle(subsumptionResolution), _subsumptionResolution(subsumptionResolution)
{
  CALL("ForwardBenchmarkWrapper::ForwardBenchmarkWrapper");
}

ForwardBenchmarkWrapper::~ForwardBenchmarkWrapper()
{
}


void ForwardBenchmarkWrapper::attach(SaturationAlgorithm *salg)
{
  CALL("ForwardBenchmarkWrapper::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));

  _forwardBenchmark.attach(salg);
  _forwardOracle.attach(salg);
  BYPASSING_ALLOCATOR
  {
    // replace the '.' with '_' in the file name
    vstring problemName = env.options->problemName();
    for (unsigned i = 0; i < problemName.length(); i++)
    {
      if (problemName[i] == '.')
      {
        problemName[i] = '_';
      }
    }
    vstring fileName = "BenchmarkResult/" + env.options->problemName();
#if USE_SAT_SUBSUMPTION_FORWARD || USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD
#if USE_SAT_SUBSUMPTION_FORWARD
    fileName += "_s";
#endif
#if USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD
    fileName += "_sr";
#endif
#if SAT_SR_IMPL == 1
    fileName += "_sat_1";
#elif SAT_SR_IMPL == 2
    fileName += "_sat_2";
#endif
#else
    fileName += "_no_sat";
#endif
#if USE_OPTIMIZED_FORWARD
    fileName += "_opt";
#endif
#if !CORRELATE_LENGTH_TIME
    outputFile.open(fileName.c_str());
#endif
  }
}

void ForwardBenchmarkWrapper::detach()
{
  CALL("ForwardBenchmarkWrapper::detach");
  _forwardBenchmark.detach();
  _forwardOracle.detach();
  _unitIndex = nullptr;
  _fwIndex = nullptr;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

bool ForwardBenchmarkWrapper::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  replacement = nullptr;
  premises = ClauseIterator::getEmpty();

  /* First measure the time for the method */
  ClauseIterator premiseAux;
  Clause* replacementAux = nullptr;
#if !CORRELATE_LENGTH_TIME
  auto start = chrono::high_resolution_clock::now();
#endif
  bool resultAux = _forwardBenchmark.perform(cl, replacementAux, premiseAux);
#if !CORRELATE_LENGTH_TIME
  auto stop = chrono::high_resolution_clock::now();

  auto duration = chrono::duration_cast<chrono::nanoseconds>(stop - start);
  totalDuration += duration;
  outputFile << duration.count() << endl;
#endif

  /* Then compute the output using the oracle */
  bool result = _forwardOracle.perform(cl, replacement, premises);


  if(result != resultAux || (replacement == nullptr) != (replacementAux == nullptr)) {
    if(!problemFile.is_open()) {
      BYPASSING_ALLOCATOR
      {
        vstring fileName = "BenchmarkResult/_mistakes_" + env.options->problemName() + ".txt";
        problemFile.open(fileName.c_str());
      }
    }
    problemFile << "------------------------------------------------------------" << endl;
    problemFile << "Configuration " << CONFIGURATION_FORWARD_SUBSUMPTION_AND_RESOLUTION << endl;
    problemFile << endl;
    problemFile << "ForwardBenchmarkWrapper::perform: result != resultAux" << endl;
    problemFile << "result: " << result << endl;
    problemFile << "resultAux: " << resultAux << endl;
    problemFile << "cl:             " << *cl << endl;
    if (result) {
      problemFile << "premises:       ";
      while (premises.hasNext()) {
        Clause* mcl = premises.next();
        problemFile << *mcl << endl;
      }
    } else {
      problemFile << "premises Aux:   " << endl;
      while (premiseAux.hasNext()) {
        problemFile << *premiseAux.next() << endl;
      }
    }
    if(replacement) {
      problemFile << "replacement:    " << *replacement << endl;
    }
    if (replacementAux) {
      problemFile << "replacementAux: " << *replacementAux << endl;
    }
  }
  return result;
}

void ForwardBenchmarkWrapper::printStats(std::ostream &out)
{
  out << "**** ForwardBenchmarkWrapper ****" << endl;
  out << "Total time for perform: " << ((double)totalDuration.count() / 1000000000) << " seconds" << endl;
  BYPASSING_ALLOCATOR
  {
    #if CORRELATE_LENGTH_TIME
    outputFile.close();
    #endif
    if(problemFile.is_open()) {
      problemFile.close();
    }
  }
}
