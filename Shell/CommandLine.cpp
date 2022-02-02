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

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/VString.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "SAT/Z3Interfacing.hpp"

#include "CommandLine.hpp"
#include "Options.hpp"
#include "Statistics.hpp"

namespace Shell {

CommandLine::CommandLine (int argc, char* argv [])
  : _next(argv+1),
    _last(argv+argc)
{
  CALL ("CommandLine::CommandLine");
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
  CALL ("CommandLine::interpret");

  bool fileGiven = false;
  while (_next != _last) {
    ASS(_next < _last);
    const char* arg = *_next++;
    if (strcmp(arg, "--version")==0) {
      cout<<VERSION_STRING<<endl;
#if VZ3
      cout << "Linked with Z3 " << Z3Interfacing::z3_full_version() << endl;
#endif
      exit(0);
    }
    // If --help or -h are used without arguments we still print help
    // If --help is used at all we print help
    // If -h is included at the end of the argument list we print help
    if(strcmp(arg,"--help")==0 || 
       (strcmp(arg,"-h")==0 && _next==_last) //if -h and there is no more
      ){ 
      // cout << _next << " " << _last << endl;
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
    cout << options.generateEncodedOptions() << "\n";
  }
} // CommandLine::interpret


} // namespace Shell
