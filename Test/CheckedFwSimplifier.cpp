
/*
 * File CheckedFwSimplifier.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file CheckedFwSimplifier.cpp
 * Implements class CheckedFwSimplifier.
 */

#include "Lib/DHSet.hpp"

#include "Kernel/Clause.hpp"

#include "CheckedFwSimplifier.hpp"

namespace Test
{

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

struct CheckedFwSimplifier::CheckingPerformer
: public ForwardSimplificationPerformer
{
public:
  CheckingPerformer()
  {
  }

  void perform(ClauseIterator premises, Clause* replacement)
  {
    CALL("CheckedFwSimplifier::CheckingPerformer::perform");
    ASSERTION_VIOLATION;
    INVALID_OPERATION("perform method of CheckingPerformer should never be called");
  }

  bool willPerform(Clause* premise)
  {
    CALL("CheckedFwSimplifier::CheckingPerformer::willPerform");

    if(_recording) {
      _firstCnt++;
      _resultSet.insert(premise);
      _resultsOfFirst.push(premise);
    }
    else {
      _secondCnt++;
      _resultsOfSecond.push(premise);
      if(!_resultSet.remove(premise)) {
	if(_ok) { _ok=false; cout<<endl; }
	cout<<"-the second inference yielded premise that the first one did not"<<endl;
	cout<<"query:  "<<_query->toString()<<endl;
	cout<<"result: "<<premise->toString()<<endl;
//	ASSERTION_VIOLATION;
      }
    }
    return false;
  }

  bool clauseKept()
  {
    CALL("CheckedFwSimplifier::CheckingPerformer::clauseKept");
    return true;
  }

  void resetAndStartRecording(Clause* query)
  {
    CALL("CheckedFwSimplifier::CheckingPerformer::resetAndStartRecording");

    _query=query;
    _firstCnt=0;
    _secondCnt=0;
    _ok=true;

    _resultSet.reset();
    _resultsOfFirst.reset();
    _resultsOfSecond.reset();
    _recording=true;
  }

  void startChecking()
  {
    CALL("CheckedFwSimplifier::CheckingPerformer::startChecking");

    _recording=false;
  }

  void doneChecking()
  {
    CALL("CheckedFwSimplifier::CheckingPerformer::doneChecking");

    ClauseIterator it=_resultSet.iterator();

    while(it.hasNext()) {
      Clause* cl=it.next();
      if(_ok) { _ok=false; cout<<endl; }
      cout<<"+the first inference yielded premise that the second one did not"<<endl;
      cout<<"query:  "<<_query->toString()<<endl;
      cout<<"result: "<<cl->toString()<<endl;
//    ASSERTION_VIOLATION;
    }


//    ASS_EQ(_firstCnt,_secondCnt);
    if(_firstCnt!=_secondCnt) {
      if(_ok) { _ok=false; cout<<endl; }
      cout<<"first and second inference didn't come up with the same number of premises"<<endl;
      cout<<"first:second is "<<_firstCnt<<":"<<_secondCnt<<endl;
//      INVALID_OPERATION("first and second inference didn't come up with the same premises");
    }

    if(!_ok) {
      cout<<"All results given by first:"<<endl;
      while(_resultsOfFirst.isNonEmpty()) {
	cout<<_resultsOfFirst.pop()->toString()<<endl;
      }
      cout<<"All results given by second:"<<endl;
      while(_resultsOfSecond.isNonEmpty()) {
	cout<<_resultsOfSecond.pop()->toString()<<endl;
      }
    }
  }

private:
  Clause* _query;
  bool _ok;
  bool _recording;
  DHSet<Clause*> _resultSet;
  ClauseStack _resultsOfFirst;
  ClauseStack _resultsOfSecond;
  size_t _firstCnt;
  size_t _secondCnt;
};


CheckedFwSimplifier::CheckedFwSimplifier(ForwardSimplificationEngine* fse1, ForwardSimplificationEngine* fse2)
: _fse1(fse1), _fse2(fse2)
{
  CALL("CheckedFwSimplifier::CheckedFwSimplifier");
  ASS(fse1);
  ASS(fse2);

  _chp=new CheckingPerformer();
}

CheckedFwSimplifier::~CheckedFwSimplifier()
{
  delete _chp;
}

void CheckedFwSimplifier::attach(SaturationAlgorithm* salg)
{
  CALL("CheckedFwSimplifier::attach");

  _fse1->attach(salg);
  _fse2->attach(salg);
}

void CheckedFwSimplifier::detach()
{
  CALL("CheckedFwSimplifier::detach");

  _fse1->detach();
  _fse2->detach();
}

void CheckedFwSimplifier::perform(Clause *cl, ForwardSimplificationPerformer *simplPerformer)
{
  CALL("CheckedFwSimplifier::perform");

  _chp->resetAndStartRecording(cl);
  _fse1->perform(cl, _chp);
  _chp->startChecking();
  _fse2->perform(cl, _chp);
  _chp->doneChecking();

  //perform the actual simplification
  _fse1->perform(cl, simplPerformer);
}

}



