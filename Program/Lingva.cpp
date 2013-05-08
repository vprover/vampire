/*
 * Lingva.cpp
 *
 * Implementation of the RunLingva class.
 *
 *  Created on: Mar 4, 2013
 *      Author: ioan
 */

#include "Lingva.hpp"
#include "Shell/UIHelper.hpp"

namespace Program{

void RunLingva::run()
{
  CALL("runLingva::run()");
  try{
	  runParsingAndAnalysis();
  } catch (MemoryLimitExceededException) {
	    env.beginOutput();
	    env.out() << "Memory limit exceeded\n";
	    env.endOutput();
	  } catch (TimeLimitExceededException) {
	    env.beginOutput();
	    env.out() << "Time limit exceeded\n";
	    env.endOutput();
	  }
	if (env.statistics->terminationReason == Statistics::REFUTATION){
		SYSTEM_FAIL("If you see this message something went terribely wrong!", 0);
		ASSERTION_VIOLATION;
	}
	if (env.statistics->terminationReason == Statistics::SATISFIABLE){
		env.beginOutput();
		UIHelper::outputResult(env.out());
		env.endOutput();
	}

}

/**
 * This is actually where we initialize the clang infrastructure
 * and set the options in order to get correct answers.
 * */
void RunLingva::runParsingAndAnalysis()
{
  CALL("runLingva::runParsingAndAnalysis");
  using clang::CompilerInstance;
  using clang::TargetOptions;
  using clang::TargetInfo;
  using clang::FileEntry;
  using clang::Token;
  using clang::ASTContext;
  using clang::ASTConsumer;
  using clang::Parser;

  // create a clang compiler instance
  CompilerInstance ci;
  ci.createDiagnostics(0, NULL);

  //create the target options
  TargetOptions to;
  //get the system options
  to.Triple = llvm::sys::getHostTriple();
  //create the target information
  TargetInfo *pti = TargetInfo::CreateTargetInfo(ci.getDiagnostics(), to);
  //set the target in the compiler instance
  ci.setTarget(pti);

  //create a file manager in the compiler instance
  ci.createFileManager();
  //create the source manager from the fileManager
  ci.createSourceManager(ci.getFileManager());
  //create the preprocessor
  ci.createPreprocessor();
  ci.getPreprocessorOpts().UsePredefines = false;
  //create the ASTConsumer
  Translator::MyASTConsumer *astConsumer = new Translator::MyASTConsumer();
  //pass to the ASTConsumer the while of interest
  astConsumer->SetWhileNumber(env.options->getWhileNumber());
  //pass to the consumer the function of interest
  astConsumer->SetFunctionNumber(env.options->getFunctionNumber());
  ci.setASTConsumer(astConsumer);

  ci.createASTContext();

  //open the C file
  const FileEntry *pFile = ci.getFileManager().getFile(env.options->inputFile().c_str());
  ci.getSourceManager().createMainFileID(pFile);
  ci.getDiagnosticClient().BeginSourceFile(ci.getLangOpts(),
	  &ci.getPreprocessor());
  //parse the file using the previously defined options
  clang::ParseAST(ci.getPreprocessor(), astConsumer, ci.getASTContext());
  ci.getDiagnosticClient().EndSourceFile();
}



};
