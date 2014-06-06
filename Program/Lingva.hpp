/**
 * @file: Lingva.hpp
 * Interface for running clang parsing as front-end for program analysis
 * @since: Mar 4, 2013, Vienna
 * @author: ioan
 */

#ifndef __LINGVA_HPP__
#define __LINGVA_HPP__

#include <string>
#include <iostream>


#include "Translator/MyASTConsumer.hpp"
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

using namespace Lib;
using namespace Shell;

namespace Program{

/**
 * Defines utilities for program analysis. This class
 * is the interface between vampire main file and the
 * clang/llvm parser and the program analysis mode.
 *
 */

class RunLingva{
public:
  RunLingva(){}
  void run();
  List<Unit* >* getUnits();
private:
  void runParsingAndAnalysis();
  Program::Statement* getWhileStatement();
};
};
#endif /* __LINGVA_HPP__ */
