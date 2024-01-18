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
 * @file CommandLine.cpp
 * Implements class for processing command line.
 *
 * @since 14/11/2004 Manchester
 */

#include <cstdlib>
#include <cstring>
#include <chrono>

#include "Debug/Assertion.hpp"

#include "Lib/VString.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "SAT/Z3Interfacing.hpp"

#include "CommandLine.hpp"
#include "Options.hpp"
#include "Statistics.hpp"

#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

namespace Shell {

#define STR_HELPER(x) #x
#define STR(x) STR_HELPER(x)

#define PRINT_VAR(out, VARNAME)                    \
  do {                                             \
    (out) << "\% " #VARNAME "=" STR(VARNAME) "\n"; \
  } while (false)

std::ostream& printVersion(std::ostream& out)
{
  out << VERSION_STRING << "\n";
#if VZ3
  std::cout << "Linked with Z3 " << Z3Interfacing::z3_full_version() << "\n";
#endif
  PRINT_VAR(out, VDEBUG);
  PRINT_VAR(out << "\% (BENCHMARK_S_SR) ", USE_WRAPPED_FORWARD_SUBSUMPTION_AND_RESOLUTION);
  PRINT_VAR(out << "\% (S_SR_IMPL)      ", SAT_SR_IMPL);
  PRINT_VAR(out << "\% (OPTIMIZE_S_SR)  ", USE_OPTIMIZED_FORWARD);
  PRINT_VAR(out, USE_NEW_SUBSUMPTION_AND_RESOLUTION_BACKWARD);
  PRINT_VAR(out, CORRELATE_LENGTH_TIME);
  PRINT_VAR(out, LOG_SSR_CLAUSES);
  PRINT_VAR(out, ENABLE_ROUNDS);
  PRINT_VAR(out, ENABLE_SAT_SR_CUTOFF);
  PRINT_VAR(out, PRINT_CLAUSES_SUBS);
  PRINT_VAR(out, PRINT_CLAUSE_COMMENTS_SUBS);
  PRINT_VAR(out, CHECK_SAT_SUBSUMPTION);
  PRINT_VAR(out, CHECK_SAT_SUBSUMPTION_RESOLUTION);
  PRINT_VAR(out, CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION);
  PRINT_VAR(out, USE_SAT_SUBSUMPTION_BACKWARD);
  PRINT_VAR(out, USE_SAT_SUBSUMPTION_RESOLUTION_BACKWARD);
  PRINT_VAR(out, SEPARATE_LOOPS_BACKWARD);
  std::cout << "\% high_resolution_clock: steady = " << std::chrono::high_resolution_clock::is_steady << ", tick period = " << std::chrono::high_resolution_clock::period::num << "/" << std::chrono::high_resolution_clock::period::den << "\n";
  std::cout << "\%          steady_clock: steady = " << std::chrono::steady_clock::is_steady << ", tick period = " << std::chrono::steady_clock::period::num << "/" << std::chrono::steady_clock::period::den << "\n";
  std::cout << "\%          system_clock: steady = " << std::chrono::system_clock::is_steady << ", tick period = " << std::chrono::system_clock::period::num << "/" << std::chrono::system_clock::period::den << "\n";
  subsat::print_config(out << "\% ");
  return out;
}

CommandLine::CommandLine (int argc, char* argv [])
  : _next(argv+1),
    _last(argv+argc)
{
} // CommandLine::CommandLine

/**
 * Interpret command line.
 *
 * @since 08/08/2004 flight Manchester-Frankfurt (as Options::correct), check for KIF added
 * @since 14/11/2004 Manchester, made from Options::correct
 * @since 10/04/2005 Torrevieja, handling environment added
 * @since 14/04/2005 Manchester, handling special commands (bag) added
 * @since 06/05/2007 Manchester, simplified again
 */
void CommandLine::interpret (Options& options)
{
  bool fileGiven = false;
  while (_next != _last) {
    ASS(_next < _last);
    const char* arg = *_next++;
    if (strcmp(arg, "--version")==0) {
      printVersion(std::cout);
      exit(0);
    }
    // If --help or -h are used without arguments we still print help
    // If --help is used at all we print help
    // If -h is included at the end of the argument list we print help
    if(strcmp(arg,"--help")==0 ||
       (strcmp(arg,"-h")==0 && _next==_last) //if -h and there is no more
      ){
      // std::cout << _next << " " << _last << endl;
      options.set("help","on");
      env.beginOutput();
      options.output(env.out());
      env.endOutput();
      exit(0);
    }
    if (arg[0] == '-') {
      if (_next == _last) {
	USER_ERROR((vstring)"no value specified for option " + arg);
      }
      else{
         if (arg[1] == '-') {
           options.set(arg+2,*_next, /*isLong*/ true);
         }
         else {
           options.set(arg+1,*_next, /*isLong*/ false);
        }
        _next++;
      }
    }
    else { // next is not an option but a file name
      if (fileGiven) {
	USER_ERROR("two input file names specified");
      }
      fileGiven = true;
      options.setInputFile(arg);
    }
  }
  // Don't force options if in Portfolio mode as the
  // forced options should apply to inner strategies only
  // Don't check global option constraints in Portoflio mode
  // as these are checked oon each inner strategy
  if(options.mode() != Options::Mode::PORTFOLIO){
    options.setForcedOptionValues();
    options.checkGlobalOptionConstraints();
  }
  if(options.encodeStrategy()){
    std::cout << options.generateEncodedOptions() << "\n";
  }
} // CommandLine::interpret


} // namespace Shell
