/*
 * MyASTConsumer.cpp
 *
 *      Author: ioan
 */


#include "MyASTConsumer.h"
#include "NewTranslator.h"

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
#include "llvm/Support/Host.h"

#include <iostream>

namespace Translator{

void MyASTConsumer::Initialize(clang::ASTContext& context)
{
  ctx = &context;
  source_manager = &(context.getSourceManager());
}

void MyASTConsumer::HandleTopLevelDecl(clang::DeclGroupRef d)
{

  clang::DeclGroupRef::iterator it;
  for (it = d.begin(); it != d.end(); it++) {

    clang::Decl* declaration = *it;

    if (clang::FunctionDecl::classof(declaration)) {
      ::clang::FunctionDecl* function_declaration =
	      (::clang::FunctionDecl*) declaration;
      if (function_declaration->hasBody()) {

	// do an analysis
	::clang::Stmt* body = declaration->getBody();
	::std::cout << "Analyze function "
		<< function_declaration->getDeclName().getAsString() << "; \n";
	newTranslator cc(body, ctx);
	cc.SetWhileToAnalyze(_whileToAnalyze);
	cc.RunRewriting();

      }

    }

  }

}
}
