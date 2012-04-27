/*
 * MyASTConsumer.h
 *
 *      Author: ioan
 */

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

namespace Translator{
using namespace clang;

class MyASTConsumer: public ASTConsumer {
private:
  clang::SourceManager* source_manager;
  clang::ASTContext *ctx;
  int _whileToAnalyze;

public:
  MyASTConsumer() :
    ASTConsumer()
  {
  }
  virtual ~MyASTConsumer()
  {
  }

  void Initialize(ASTContext& context);
  void SetWhileNumber(int wno)
  {
    _whileToAnalyze = wno;
  }

  virtual void HandleTopLevelDecl(DeclGroupRef d);
};
}

