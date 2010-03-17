/**
 * @file CodeTreeInterfaces.cpp
 * Implements indexing structures that use code trees.
 *
 */

#include "../Lib/Allocator.hpp"
#include "../Lib/Recycler.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Renaming.hpp"
#include "../Kernel/SubstHelper.hpp"
#include "../Kernel/Term.hpp"

#include "CodeTreeInterfaces.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

class CodeTreeSubstitution
: public ResultSubstitution
{
public:
  CodeTreeSubstitution(TermCodeTree::TermEContext* ctx, Renaming* resultNormalizer)
  : _ctx(ctx), _resultNormalizer(resultNormalizer),
  _applicator(0)
  {}
  ~CodeTreeSubstitution()
  {
    if(_applicator) {
      delete _applicator;
    }
  }

  TermList applyToBoundResult(TermList t)
  { return SubstHelper::apply(t, *getApplicator()); }

  Literal* applyToBoundResult(Literal* lit)
  { return SubstHelper::apply(lit, *getApplicator()); }

  bool isIdentityOnQueryWhenResultBound() {return true;}
private:
  struct Applicator
  {
    inline
    Applicator(TermCodeTree::TermEContext* ctx, Renaming* resultNormalizer)
    : _ctx(ctx), _resultNormalizer(resultNormalizer) {}
    TermList apply(unsigned var)
    {
      ASS(_resultNormalizer->contains(var));
      unsigned nvar=_resultNormalizer->get(var);
      return _ctx->bindings[nvar];
    }
  private:
    TermCodeTree::TermEContext* _ctx;
    Renaming* _resultNormalizer;
  };

  Applicator* getApplicator()
  {
    if(!_applicator) {
      _applicator=new Applicator(_ctx, _resultNormalizer);
    }
    return _applicator;
  }

  TermCodeTree::TermEContext* _ctx;
  Renaming* _resultNormalizer;
  Applicator* _applicator;
};


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

class CodeTreeTIS::ResultIterator
: public IteratorCore<TermQueryResult>
{
public:
  ResultIterator(CodeTreeTIS* tree, TermList t, bool retrieveSubstitutions)
  : _retrieveSubstitutions(retrieveSubstitutions),
    _found(0), _finished(false), _tree(tree)
  {
    if(_retrieveSubstitutions) {
      NOT_IMPLEMENTED;
    }
    Recycler::get(_ctx);
    _ctx->init(t,&_tree->_ct);
  }

  ~ResultIterator()
  {
    _ctx->deinit(&_tree->_ct);
    Recycler::release(_ctx);
  }

  bool hasNext()
  {
    CALL("CodeTreeTIS::ResultIterator::hasNext");

    if(_found) {
      return true;
    }
    if(_finished) {
      return false;
    }
    void* data;
    if(TermCodeTree::next(*_ctx, data)) {
      _found=static_cast<TermInfo*>(data);
    }
    else {
      _found=0;
      _finished=true;
    }
    return _found;
  }

  TermQueryResult next()
  {
    CALL("CodeTreeTIS::ResultIterator::next");
    ASS(_found);

    TermQueryResult res(_found->t, _found->lit, _found->cls);
    _found=0;
    return res;
  }
private:

  bool _retrieveSubstitutions;
  TermInfo* _found;
  bool _finished;
  CodeTreeTIS* _tree;
  TermCodeTree::TermEContext* _ctx;
};

void CodeTreeTIS::insert(TermList t, Literal* lit, Clause* cls)
{
  CALL("CodeTreeTIS::insert");
  ASS_EQ(_ct._initEContextCounter,0); //index must not be modified while traversed

  static CodeTree::CodeStack code;
  code.reset();

  _ct.compile(t,code);
  ASS_EQ(code.top().instr(), CodeTree::SUCCESS);

  //assign the term info
  code.top().result=new TermInfo(t,lit,cls);
  ASS_EQ(code.top().instr()&3, CodeTree::SUCCESS);

  _ct.incorporate(code);
}

void CodeTreeTIS::remove(TermList t, Literal* lit, Clause* cls)
{
  CALL("CodeTreeTIS::remove");
  ASS_EQ(_ct._initEContextCounter,0); //index must not be modified while traversed

  //TODO: implement deletion that frees unnecessary memory

  TermInfo ti(t,lit,cls);

  static TermCodeTree::TermEContext ctx;
  ctx.init(t, &_ct);

  void* data;
  do {
    //we delete only terms that are present, so 'not found' is not possible
    ALWAYS(TermCodeTree::next(ctx, data));
  } while(ti!=*static_cast<TermInfo*>(data));

  ASS_EQ(ctx.op->instr()&3, CodeTree::SUCCESS);
  *ctx.op=CodeTree::OpCode(CodeTree::FAIL);

  ctx.deinit(&_ct);
}

TermQueryResultIterator CodeTreeTIS::getGeneralizations(TermList t, bool retrieveSubstitutions)
{
  CALL("CodeTreeTIS::getGeneralizations");

  return vi( new ResultIterator(this, t, retrieveSubstitutions) );
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
  bool res=TermCodeTree::next(ctx, aux);

  ctx.deinit(&_ct);
  return res;
}


}
