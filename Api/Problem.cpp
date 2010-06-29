/**
 * @file Problem.cpp
 * Implements class Problem.
 */

#include "Problem.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/List.hpp"

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

void Problem::addFormula(AnnotatedFormula f)
{
  CALL("Problem::addFormula");

  AFList::push(f,_data->_forms);
}

void Problem::addFromStream(istream s, string includeDirectory, bool simplifySyntax)
{
  CALL("Problem::addFromStream");

}

Problem Problem::clone()
{
  CALL("Problem::clone");

  Problem res;
  _data->cloneInto(res._data);
  return res;
}

Problem Problem::clausify()
{
  CALL("Problem::clausify");

  Problem res;

  NOT_IMPLEMENTED;

  return res;
}

///////////////////////////////////////
// Iterating through the problem

bool AnnotatedFormulaIterator::hasNext()
{

}

AnnotatedFormula AnnotatedFormulaIterator::next()
{

}

void AnnotatedFormulaIterator::del()
{

}


AnnotatedFormulaIterator Problem::formulas()
{

}


}
