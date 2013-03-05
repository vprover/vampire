/*
 * Lingva.hpp
 *
 *  Created on: Mar 4, 2013
 *      Author: ioan
 */

#ifndef LINGVA_HPP_
#define LINGVA_HPP_

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

using namespace Lib;
using namespace Shell;
using namespace Shell::CASC;

namespace Program{

/**
 * Defines utilities for program analysis. This class
 * is the interface between vampire main file and the
 * clang/llvm parser and the program analysis mode.
 *
 */

class RunLingva{
public:
  /**
   * Call the parser on @param fileName and than call the
   * analyzer on this file, according to the setted options.
   * */
  RunLingva(const char* fileName): _file(fileName) {};
  void run();
private:
  /**
   * This is actually where we initialize the clang infrastructure
   * and set the options in order to get correct answers.
   * */
  void runParsingAndAnalysis();
  /**
   * Input filename. The other way of doing this can be by simply
   * by accessing the env.options->inputFile();
   */
  const char* _file;
};
};
#endif /* LINGVA_HPP_ */
