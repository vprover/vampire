/**
 * @file CodeTreeInterfaces.cpp
 * Implements indexing structures that use code trees.
 *
 */

#include "../Lib/Allocator.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"

#include "CodeTreeInterfaces.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

struct CodeTreeTIS::TermInfo
{
  TermInfo(TermList t, Literal* lit, Clause* cls)
  : t(t), lit(lit), cls(cls) {}

  inline bool operator==(const TermInfo& o)
  { return cls==o.cls && lit==o.lit && t==o.t; }

  inline bool operator!=(const TermInfo& o)
  { return !(*this==o); }

  CLASS_NAME("CodeTreeTIS::TermInfo");
  USE_ALLOCATOR(TermInfo);

  TermList t;
  Literal* lit;
  Clause* cls;
};

void CodeTreeTIS::insert(TermList t, Literal* lit, Clause* cls)
{
  CALL("CodeTreeTIS::insert");

  static CodeTree::CodeStack code;
  code.reset();

  _ct.compile(t,code);
  ASS_EQ(code.top().instr(), CodeTree::SUCCESS);

  //assign the term info
  code.top().result=new TermInfo(t,lit,cls);
  ASS_EQ(code.top().instr(), CodeTree::SUCCESS);

  _ct.incorporate(code);
}

void CodeTreeTIS::remove(TermList t, Literal* lit, Clause* cls)
{
  CALL("CodeTreeTIS::remove");

  //TODO: implement deletion that frees unnecessary memory

  TermInfo ti(t,lit,cls);

  static TermCodeTree::TermEContext ctx;
  ctx.init(t, &_ct);

  void* data;
  do {
    //we delete only terms that are present, so 'not found' is not possible
    ALWAYS(_ct.next(ctx, data));
  } while(ti!=*static_cast<TermInfo*>(data));

  ASS_EQ(ctx.op->instr(), CodeTree::SUCCESS);
  *ctx.op=CodeTree::OpCode(CodeTree::FAIL);

  ctx.deinit();
}

TermQueryResultIterator CodeTreeTIS::getGeneralizations(TermList t, bool retrieveSubstitutions)
{
  CALL("CodeTreeTIS::getGeneralizations");

  if(retrieveSubstitutions) {
    NOT_IMPLEMENTED;
  }

  NOT_IMPLEMENTED;
}

bool CodeTreeTIS::generalizationExists(TermList t)
{
  CALL("CodeTreeTIS::generalizationExists");

  if(!_ct._data) {
    return false;
  }

  static TermCodeTree::TermEContext ctx;
  ctx.init(t, &_ct);

  void* aux;
  bool res=_ct.next(ctx, aux);

  ctx.deinit();
  return res;
}


}
