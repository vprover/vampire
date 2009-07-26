/**
 * @file Grounding.cpp
 * Implements class Grounding.
 */

#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Stack.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/SubstHelper.hpp"
#include "../Kernel/Term.hpp"

#include "Grounding.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

struct Grounding::GroundingApplicator
{
  GroundingApplicator()
  {
    int funcs=env.signature->functions();
    for(int i=0;i<funcs;i++) {
      if(env.signature->functionArity(i)==0) {
        _constants.push(TermList(Term::create(i,0,0)));
      }
    }
    if(_constants.size()) {
      _maxIndex=_constants.size()-1;
    }
  }

  void initForClause(Clause* cl)
  {
    _varNumbering.reset();
    int nextNum=0;
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      Literal* lit=(*cl)[i];
      Term::VariableIterator vit(lit);
      while(vit.hasNext()) {
	unsigned var=vit.next().var();
	if(_varNumbering.insert(var,nextNum)) {
	  nextNum++;
	}
      }
    }
    _varCnt=nextNum;
    _indexes.init(_varCnt, 0);
    _beforeFirst=true;
  }

  bool newAssignment()
  {
    if(_beforeFirst) {
      _beforeFirst=false;
      return _constants.size()>0 || _varCnt==0;
    }
    int incIndex=_varCnt-1;
    while(incIndex>=0 && _indexes[incIndex]==_maxIndex) {
      _indexes[incIndex]=0;
      incIndex--;
    }
    if(incIndex==-1) {
      return false;
    }
    _indexes[incIndex]++;
    return true;
  }

  TermList apply(unsigned var)
  {
    return _constants[_indexes[_varNumbering.get(var)]];
  }

private:
  DHMap<unsigned, unsigned, IdentityHash> _varNumbering;
  Stack<TermList> _constants;
  DArray<unsigned> _indexes;
  unsigned _maxIndex;
  int _varCnt;
  bool _beforeFirst;
};

ClauseList* Grounding::simplyGround(ClauseIterator clauses)
{
  CALL("Grounding::simplyGround");

  GroundingApplicator ga;
  ClauseList* res=0;

  while(clauses.hasNext()) {
    Clause* cl=clauses.next();
    unsigned clen=cl->length();

    ga.initForClause(cl);
    while(ga.newAssignment()) {
      Clause* rcl=new(clen) Clause(clen, cl->inputType(), new Inference1(Inference::GROUNDING, cl));
      rcl->setAge(cl->age());

      for(unsigned i=0;i<clen;i++) {
	(*rcl)[i]=SubstHelper::apply((*cl)[i], ga);
      }

//      cout<<(*rcl)<<endl;
      ClauseList::push(rcl, res);
    }
  }

  return res;
}

}
