/**
 * @file MyASTConsumer.cpp
 * @author Ioan Dragan
 */

#include <iostream>

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

#include "MyASTConsumer.hpp"
#include "NewTranslator.hpp"
#include "Lib/List.hpp"
#include "Program/Variable.hpp"

using namespace Translator;

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
      function_number++;
      cout << "Function number: "<<function_number<<endl;

      ::clang::FunctionDecl* function_declaration =
	      (::clang::FunctionDecl*) declaration;
      cout<< "Function Name : " <<function_declaration->getDeclName().getAsString()<<endl;
      if (function_declaration->hasBody() && (_functionNumber == function_number || _whileToAnalyze==-1 || _functionNumber == 0)) {
	const clang::SourceLocation sl = function_declaration->getLocStart();
	//sl.dump(*source_manager);
	// do an analysis
	::clang::Stmt* body = declaration->getBody();
	//::std::cout << "Analyze function "
	//	<< function_declaration->getDeclName().getAsString() << "; \n";
	_cc = new newTranslator(body, ctx);
	_cc->SetWhileToAnalyze(_whileToAnalyze);
	if(_whileToAnalyze == -1)
	  {
	  _cc->RunRewriting();
	  }
      }

    }
  }
}

Program::Statement* MyASTConsumer::getWhile(){
  CALL("MyASTConsumer::getWhile()");
  if(_functionNumber > function_number || _functionNumber <= 0)
      USER_ERROR("There are fewer functions than you expect in the file! \n Check the function number you want to analyze!");

  return _cc->getWhile(_whileToAnalyze);
}

void MyASTConsumer::runAnalysis(){
  CALL("MyASTConsumer::runAnalysis");
  if(_functionNumber > function_number || _functionNumber <= 0 )
    USER_ERROR("There are fewer functions than you expect in the file! \n Check the function number you want to analyze!");

  _cc->RunRewriting();
}
