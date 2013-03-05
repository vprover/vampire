/*
 * Lingva.cpp
 *
 * Implementation of the RunLingva class.
 *
 *  Created on: Mar 4, 2013
 *      Author: ioan
 */

#include "Lingva.hpp"

namespace Program{

void RunLingva::run()
{
  CALL("runLingva::run()");
  runParsingAndAnalysis();
}

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
  astConsumer->SetFunctionNumber(env.options->getFunctionNumber());
  ci.setASTConsumer(astConsumer);

  ci.createASTContext();

  const FileEntry *pFile = ci.getFileManager().getFile(_file);
  ci.getSourceManager().createMainFileID(pFile);
  ci.getDiagnosticClient().BeginSourceFile(ci.getLangOpts(),
	  &ci.getPreprocessor());
  clang::ParseAST(ci.getPreprocessor(), astConsumer, ci.getASTContext());
  ci.getDiagnosticClient().EndSourceFile();
}

};
