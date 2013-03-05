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

class runLingva{
public:
  runLingva(const char* fileName): _file(fileName) {};
  void run();
private:
  void runParsingAndAnalysis();
  const char* _file;
};

#endif /* LINGVA_V1_HPP_ */
