#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/LiteralIndex.hpp"
#include <chrono>

#include "SATSubsumption/ForwardSubsumptionAndResolutionWrapper.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

static chrono::_V2::system_clock::duration totalDuration = chrono::duration<int64_t, std::nano>::zero();
static ofstream outputFile;

ForwardSubsumptionAndResolutionWrapper::ForwardSubsumptionAndResolutionWrapper(bool subsumptionResolution) : _forwardSubsumptionAndResolution(subsumptionResolution), _forwardOracle(subsumptionResolution), _subsumptionResolution(subsumptionResolution)
{
  CALL("ForwardSubsumptionAndResolutionWrapper::ForwardSubsumptionAndResolutionWrapper");
}

ForwardSubsumptionAndResolutionWrapper::~ForwardSubsumptionAndResolutionWrapper()
{
}

void ForwardSubsumptionAndResolutionWrapper::attach(SaturationAlgorithm *salg)
{
  CALL("ForwardSubsumptionAndResolutionWrapper::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));

  _forwardSubsumptionAndResolution.attach(salg);
  _forwardOracle.attach(salg);

  BYPASSING_ALLOCATOR
  {
    vstring fileName = "timeForPerform_" + env.options->problemName();
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
#endif
    outputFile.open(fileName.c_str());
  }
}

void ForwardSubsumptionAndResolutionWrapper::detach()
{
  CALL("ForwardSubsumptionAndResolutionWrapper::detach");
  _forwardSubsumptionAndResolution.detach();
  _forwardOracle.detach();
  _unitIndex = nullptr;
  _fwIndex = nullptr;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

bool ForwardSubsumptionAndResolutionWrapper::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  /* First measure the time for the method */
  auto start = chrono::high_resolution_clock::now();
  ClauseIterator premiseAux;
  _forwardSubsumptionAndResolution.perform(cl, replacement, premiseAux);
  auto stop = chrono::high_resolution_clock::now();
  auto duration = chrono::duration_cast<chrono::nanoseconds>(stop - start);
  totalDuration += duration;
  outputFile << duration.count() << endl;
  /* Then compute the output using the oracle */
  return _forwardOracle.perform(cl, replacement, premises);
}

void ForwardSubsumptionAndResolutionWrapper::printStats(std::ostream &out)
{
  out << "**** ForwardSubsumptionAndResolutionWrapper ****" << endl;
  out << "Total time for perform: " << ((double)totalDuration.count() / 1000000000) << " seconds" << endl;
  BYPASSING_ALLOCATOR
  {
    outputFile.close();
  }
}
