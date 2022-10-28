#include "SATSubsumption.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"


#if ENABLE_BENCHMARK


// Google benchmark library
// https://github.com/google/benchmark
#include <benchmark/benchmark.h>

void SATSubsumption::ProofOfConcept::add_common_benchmark_args(vvector<vstring>& args)
{
  if (!env.options->benchmarkOut().empty()) {
    vstringstream s;
    s << "--benchmark_out=" << env.options->benchmarkOut();
    args.push_back(s.str());
    args.push_back("--benchmark_out_format=json");
  }

  if (env.options->benchmarkRepetitions() > 0) {
    vstringstream s;
    s << "--benchmark_repetitions=" << std::to_string(env.options->benchmarkRepetitions());
    args.push_back(s.str());
  }
}

void SATSubsumption::ProofOfConcept::init_benchmark(vvector<vstring> the_args)
{
  // Need to keep the strings alive while benchmarking is in progress
  static vvector<vstring> args;
  static vvector<char*> c_args;

  if (!args.empty() || !c_args.empty()) {
    std::cerr << "ERROR: init_benchmark should only be called once!" << std::endl;
    std::abort();
  }

  args = std::move(the_args);
  add_common_benchmark_args(args);

  for (vstring& arg : args) {
    // NOTE: non-const overload of std::string::data was only added in C++17
    char* x = const_cast<char*>(arg.data());
    c_args.push_back(x);
  }

  char** argv = c_args.data();
  int argc = c_args.size();

  benchmark::Initialize(&argc, argv);
}

#endif
