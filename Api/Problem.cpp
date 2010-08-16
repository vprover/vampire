/**
 * @file Problem.cpp
 * Implements class Problem.
 */

#include "Problem.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/CNF.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/LispLexer.hpp"
#include "Shell/LispParser.hpp"
#include "Shell/Naming.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Options.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/SimplifyFalseTrue.hpp"
#include "Shell/SimplifyProver.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"


namespace Api
{

using namespace Lib;

typedef List<AnnotatedFormula> AFList;

class Problem::PData
{
public:
  PData() : _forms(0), _refCnt(0)
  {
  }
  ~PData()
  {
    _forms->destroy();
  }

  void incRef() { _refCnt++; }
  void decRef()
  {
    ASS_G(_refCnt,0);
    _refCnt--;
    if(!_refCnt) {
      delete this;
    }
  }

  void cloneInto(PData* obj)
  {
    CALL("Problem::PData::cloneInto");
    ASS_EQ(obj->_forms, 0);

    obj->_forms=_forms->copy();
  }

  AFList* _forms;
private:
  unsigned _refCnt;
};


Problem::Problem()
{
  CALL("Problem::Problem");

  _data=new PData;
  _data->incRef();
}

Problem::Problem(const Problem& p)
{
  CALL("Problem::Problem(const Problem&)");

  _data=const_cast<PData*>(p._data);
  _data->incRef();
}

Problem& Problem::operator=(const Problem& p)
{
  CALL("Problem::operator =");

  PData* oldData=_data;

  _data=const_cast<PData*>(p._data);

  _data->incRef();
  oldData->decRef();

  return *this;
}

Problem::~Problem()
{
  CALL("Problem::~Problem");

  _data->decRef();
}

Problem Problem::clone()
{
  CALL("Problem::clone");

  Problem res;
  _data->cloneInto(res._data);
  return res;
}

void Problem::addFormula(AnnotatedFormula f)
{
  CALL("Problem::addFormula");

  AFList::push(f,_data->_forms);
}


///////////////////////////////////////
// Parsing

void Problem::addFromStream(istream& s, string includeDirectory, bool simplifySyntax)
{
  CALL("Problem::addFromStream");

  using namespace Shell;

  string originalInclude=env.options->include();
  env.options->setInclude(includeDirectory);

  Kernel::UnitList* units;
  if(simplifySyntax) {
    LispLexer lexer(s);
    LispParser parser(lexer);
    LispParser::Expression* expr = parser.parse();
    SimplifyProver simplify;
    units = simplify.units(expr);
  }
  else {
    TPTPLexer lexer(s);
    TPTPParser parser(lexer);
    units = parser.units();
  }

  env.options->setInclude(originalInclude);

  while(units) {
    Kernel::Unit* u=Kernel::UnitList::pop(units);
    addFormula(AnnotatedFormula(u));
  }
}


///////////////////////////////////////
// Clausification

struct Problem::Clausifier
{
  Clausifier(Problem* res) : res(res), naming(env.options->naming()) {}

  void clausify(Kernel::Unit* unit)
  {
    CALL("Problem__Clausifier::clausify");

    using namespace Shell;

    if(unit->isClause()) {
      res->addFormula(AnnotatedFormula(unit));
      return;
    }
    unit = Rectify::rectify(unit);
    unit = SimplifyFalseTrue::simplify(unit);
    unit = Flattening::flatten(unit);
    unit = NNF::ennf(unit);
    unit = Flattening::flatten(unit);

    Kernel::UnitList* newDefs;
    unit = naming.apply(unit,newDefs);

    for(;;) {
      unit = NNF::nnf(unit);
      unit = Flattening::flatten(unit);
      unit = Skolem::skolemise(unit);

      cnf.clausify(unit,auxClauseStack);
      while (! auxClauseStack.isEmpty()) {
	Unit* u = auxClauseStack.pop();
	res->addFormula(AnnotatedFormula(u));
      }

      if(newDefs==0) {
	break;
      }
      unit=UnitList::pop(newDefs);
    }
  }

  Problem* res;
  Shell::CNF cnf;
  Stack<Kernel::Clause*> auxClauseStack;
  Shell::Naming naming;
};

Problem Problem::clausify()
{
  CALL("Problem::clausify");

  Problem res;

  {
    Clausifier clausifier(&res);

    AnnotatedFormulaIterator fit=formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      clausifier.clausify(f);
    }
  }

  return res;
}

///////////////////////////////////////
// Iterating through the problem

bool AnnotatedFormulaIterator::hasNext()
{
  CALL("AnnotatedFormulaIterator::hasNext");

  AFList** plst=static_cast<AFList**>(idata);

  if(ready) {
    return *plst;
  }
  //we need to advance to the next element of the list
  ASS(*plst); //we're not at the end of the list
  plst=(*plst)->tailPtr();
  idata=plst;
  ready=true;
  return *plst;
}

AnnotatedFormula AnnotatedFormulaIterator::next()
{
  CALL("AnnotatedFormulaIterator::next");

  AFList** plst=static_cast<AFList**>(idata);
  ASS(ready);
  ASS(*plst); //we're not at the end of the list
  ready=false;
  return (*plst)->head();
}

void AnnotatedFormulaIterator::del()
{
  CALL("AnnotatedFormulaIterator::del");

  AFList** plst=static_cast<AFList**>(idata);
  ASS(*plst); //we're not at the end of the list

  AFList* removedLink=*plst;
  *plst=removedLink->tail();
  delete removedLink;
}


AnnotatedFormulaIterator Problem::formulas()
{
  CALL("Problem::formulas");

  AnnotatedFormulaIterator res;
  res.idata=&_data->_forms;
  res.ready=true;
  return res;
}


}
