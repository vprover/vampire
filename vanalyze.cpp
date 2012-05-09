/*
 *
 *  Created on: Mar, 2012
 *      Author: ioan
 */

/**
 * created from @file vutil.cpp.
 * Implements the main function for running small tools thet use Vampire's infrastructure.
 */

#include <string>
#include <iostream>


#include "Translator/MyASTConsumer.h"
#include "llvm/Support/Host.h"

#include "clang/Frontend/CompilerInstance.h"
#include "clang/Basic/TargetOptions.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Parse/Parser.h"
#include "clang/Parse/ParseAST.h"
#include "Forwards.hpp"

#include "Debug/Log.hpp"
#include "Debug/Tracer.hpp"


#include "Api/ResourceLimits.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/CASC/CASCMode.hpp"

#include "VUtils/AnnotationColoring.hpp"
#include "VUtils/CPAInterpolator.hpp"
#include "VUtils/DPTester.hpp"
#include "VUtils/EPRRestoringScanner.hpp"
#include "VUtils/FOEquivalenceDiscovery.hpp"
#include "VUtils/PreprocessingEvaluator.hpp"
#include "VUtils/ProblemColoring.hpp"
#include "VUtils/SimpleSMT.hpp"
#include "VUtils/SMTLIBConcat.hpp"
#include "VUtils/Z3InterpolantExtractor.hpp"

using namespace Lib;
using namespace Shell;
using namespace Shell::CASC;
using namespace VUtils;


void runParsingAndAnalysis(const char* file)
{
	using clang::CompilerInstance;
	using clang::TargetOptions;
	using clang::TargetInfo;
	using clang::FileEntry;
	using clang::Token;
	using clang::ASTContext;
	using clang::ASTConsumer;
	using clang::Parser;

	CompilerInstance ci;
	ci.createDiagnostics(0, NULL);

	TargetOptions to;
	to.Triple = llvm::sys::getHostTriple();
	TargetInfo *pti = TargetInfo::CreateTargetInfo(ci.getDiagnostics(), to);
	ci.setTarget(pti);

	ci.createFileManager();
	ci.createSourceManager(ci.getFileManager());
	ci.createPreprocessor();
	ci.getPreprocessorOpts().UsePredefines = false;
	Translator::MyASTConsumer *astConsumer = new Translator::MyASTConsumer();
	astConsumer->SetWhileNumber(env.options->getWhileNumber());
	ci.setASTConsumer(astConsumer);
	
	ci.createASTContext();

	const FileEntry *pFile = ci.getFileManager().getFile(file);
	ci.getSourceManager().createMainFileID(pFile);
	ci.getDiagnosticClient().BeginSourceFile(ci.getLangOpts(),
						&ci.getPreprocessor());
	clang::ParseAST(ci.getPreprocessor(), astConsumer, ci.getASTContext());
	ci.getDiagnosticClient().EndSourceFile();
	}

void explainException (Exception& exception)
{
  env.beginOutput();
  exception.cry(env.out());
  env.endOutput();
} // explainException

void readAndFilterGlobalOpts(Stack<char*>& args) {
  Stack<char*>::StableDelIterator it(args);
  char* filename;
  //skip the first item which is the executable name
  ALWAYS(it.hasNext());
  it.next();

  while(it.hasNext()) {
    string arg(it.next());
    if(arg=="-tr") {
      it.del();
      if(!it.hasNext()) {
	USER_ERROR("value for -tr option expected");
      }
      string traceStr(it.next());
      it.del();
      PROCESS_TRACE_SPEC_STRING(traceStr);
    }
    else if(arg=="-m") {
      it.del();
      if(!it.hasNext()) {
	USER_ERROR("value for -m option expected");
      }
      string memLimitStr = it.next();
      it.del();
      unsigned memLimit;
      if(!Int::stringToUnsignedInt(memLimitStr, memLimit)) {
	USER_ERROR("unsigned number expected as value of -m option");
      }
      env.options->setMemoryLimit(memLimit);
      Allocator::setMemoryLimit(env.options->memoryLimit()*1048576ul);
    }
    else if(arg == "-wno" || arg == "while_number"){
    	it.del();
    	if(!it.hasNext()) {
    		USER_ERROR("value for -wno option expected");
    	      }
    	string whileString = it.next();
    	it.del();

    	int no;
    	if(!Int::stringToInt(whileString, no))
    		USER_ERROR("integer number expected");
    //	env.options->setWhileNumber(no);
    }
    else if(arg == "-in"){
    	it.del();
    	    	if(!it.hasNext()) {
    	    		USER_ERROR("value for -in option expected");
    	    	      }
    	    	filename=it.next();
    	    	it.del();
    }
    else
    {
      break;
    }
  }
}

/**
 * The main function.
  */
int main(int argc, char* argv [])
{
  CALL ("main");

  int resultValue=2;

  System::registerArgv0(argv[0]);
  System::setSignalHandlers();
  Api::ResourceLimits::disableLimits();
   // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  Shell::CommandLine cl(argc,argv);
  cl.interpret(*env.options);
  
  try {
    env.options->setMode(Options::MODE_VAMPIRE);
    env.options->setTimeLimitInDeciseconds(0);


    Allocator::setMemoryLimit(1024u*1048576ul);

    string inputFile = env.options->inputFile();
    if(inputFile=="") {
      USER_ERROR("Cannot open problem file: "+inputFile);
    }
    else {
     runParsingAndAnalysis(inputFile.c_str());
    }
/*
       const char *fim;
       string opt = env.options->inputFile();
       fim = opt.c_str();
       runParsingAndAnalysis(fim);*/
  }
#if VDEBUG
  catch (Debug::AssertionViolationException& exception) {
    reportSpiderFail();
  }
#endif
  catch (UserErrorException& exception) {
    reportSpiderFail();
    explainException(exception);
  }
  catch (Exception& exception) {
    reportSpiderFail();
    env.beginOutput();
    explainException(exception);
    env.statistics->print(env.out());
    env.endOutput();
  }
  catch (std::bad_alloc& _) {
    reportSpiderFail();
    env.beginOutput();
    env.out() << "Insufficient system memory" << '\n';
    env.endOutput();
  }
//   delete env.allocator;

  return resultValue;
} // main









