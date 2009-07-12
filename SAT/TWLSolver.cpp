/**
 * @file TWLSolver.cpp
 * Implements class TWLSolver.
 */


#include "../Debug/Assertion.hpp"

#include "../Lib/Array.hpp"
#include "../Lib/Environment.hpp"

#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "TWLSolver.hpp"

#define LOG(x)
//#define LOG(x) cout<<x<<endl

namespace SAT
{

using namespace Lib;

TWLSolver::TWLSolver()
: _status(SATISFIABLE), _assignment(0), _assignmentLevels(0),
_windex(0), _unprocessed(0), _varCnt(0), _level(1)
{

}

void TWLSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("TWLSolver::ensureVarCnt");

  if(newVarCnt<=_varCnt) {
    return;
  }

  _assignment.expand(newVarCnt);
  _assignmentLevels.expand(newVarCnt);
  _assignmentPremises.expand(newVarCnt);
  for(unsigned i=_varCnt;i<newVarCnt;i++) {
    _assignment[i]=AS_UNDEFINED;
    _assignmentPremises[i]=0;
  }

  _windex.expand(newVarCnt*2);
  _unprocessed.expand(newVarCnt+1);

  _varCnt=newVarCnt;
}



void TWLSolver::backtrack(unsigned tgtLevel)
{
  CALL("TWLSolver::backtrack");
  ASSERT_VALID(*this);

  static Stack<USRec> marks;
  static Stack<unsigned> toPropagate;
  static ZIArray<unsigned> varMarkTgts;
  static ZIArray<AsgnVal> prevAssignments;

  if(tgtLevel==_level) {
    return;
  }

bt_start:

  if(tgtLevel==0) {
    throw UnsatException();
  }

  ASS(marks.isEmpty());

  USRec rec;
  for(;;) {
    rec=_unitStack.pop();
    if(rec.mark) {
      if(varMarkTgts[rec.var]==0 || varMarkTgts[rec.var]>rec.markTgtLevel) {
	marks.push(rec);
	varMarkTgts[rec.var]=rec.markTgtLevel;
      }
    }
    ASS(!rec.mark || rec.markTgtLevel>=_assignmentLevels[rec.var]);
    if(_assignment[rec.var]!=AS_UNDEFINED && (!rec.mark || rec.markedIsDefining)) {
      prevAssignments[rec.var]=_assignment[rec.var];
      _assignment[rec.var]=AS_UNDEFINED;
    }
    if(rec.choice) {
      _level--;
      incorporateUnprocessed();
      ASS_GE(_level, tgtLevel);
      if(_level==tgtLevel) {
	break;
      }
    }
  };

  ASS(toPropagate.isEmpty());

  while(marks.isNonEmpty()) {
    USRec rec=marks.pop();
    ASS_NEQ(varMarkTgts[rec.var], 0);
    ASS(rec.mark);
    if(varMarkTgts[rec.var]<rec.markTgtLevel) {
      continue;
    }
    varMarkTgts[rec.var]=0;

    if(rec.mark && rec.markTgtLevel>_level) {
      continue;
    }
    if(rec.mark && rec.markTgtLevel==_level) {
      rec.mark=false;
    }
    ASS_LE(_assignmentLevels[rec.var],_level);
    if(_assignment[rec.var]==AS_UNDEFINED) {
      _assignment[rec.var]=prevAssignments[rec.var];
      //the _assignmentPremises[rec.var] and _assignmentLevels[rec.var]
      //values are properly assigned from the previous time
      rec.markedIsDefining=true;

      toPropagate.push(rec.var);
    }

    _unitStack.push(rec);
  }

  while(toPropagate.isNonEmpty()) {
    unsigned propVar=toPropagate.pop();
    unsigned propBtLev=propagate(propVar);
    tgtLevel=min(tgtLevel, propBtLev);
  }

  if(tgtLevel!=_level) {
    ASS_L(tgtLevel, _level);
    goto bt_start;
  }

  LOG("backtracked to level "<<_level);

}

void TWLSolver::incorporateUnprocessed()
{
  CALL("TWLSolver::incorporateUnprocessed");

  Stack<SATClause*>& unp=_unprocessed[_level];
  while(unp.isNonEmpty()) {
    SATClause* cl=unp.pop();
    //unprocessed literals must already have literals
    //to be watched in the right place
    insertIntoWatchIndex(cl);
  }
}

unsigned TWLSolver::getBacktrackLevel(SATClause* conflictClause)
{
  CALL("TWLSolver::getBacktrackLevel");
  ASSERT_VALID(*this);

  unsigned btLev=0;
  static Stack<SATClause*> confCls;
  static DHMap<unsigned,bool,IdentityHash> checked;
  confCls.reset();
  checked.reset();

  confCls.push(conflictClause);

//  cout<<endl<<"conf: "<<(*conflictClause)<<endl;
//  printAssignment();

  while(confCls.isNonEmpty()) {
    SATClause* ccl=confCls.pop();
    unsigned cclen=ccl->length();
    for(unsigned i=0; i<cclen; i++) {
      unsigned lvar=(*ccl)[i].var();
//      if(_assignment[lvar]==AS_UNDEFINED) {
//	LOG("lvar: "<<lvar);
//	printAssignment();
//      }

      ASS_NEQ(_assignment[lvar], AS_UNDEFINED);
      if(_assignmentLevels[lvar]<=btLev+1) {
	continue;
      }
      if(!checked.insert(lvar, true)) {
	//we've already visited this variable
	continue;
      }
      SATClause* icl=_assignmentPremises[lvar];
      if(icl) {
	if(icl!=ccl) {
	  confCls.push(icl);
	}
      } else {
	btLev=max(btLev, _assignmentLevels[lvar]-1);
      }
    }
  }
  ASS_L(btLev, _level);
  return btLev;
}


unsigned TWLSolver::propagate(unsigned var0)
{
  CALL("TWLSolver::propagate");

  static Stack<unsigned> toDo;
  toDo.reset();
  toDo.push(var0);
  while(toDo.isNonEmpty()) {
    unsigned var=toDo.pop();
    LOG("propagating "<<var<<" "<<_assignment[var]);

    //the _windex index is of the opposite literal
    unsigned wiIndex=var*2+( (_assignment[var]==AS_FALSE) ? 1 : 0 );

//    {
//      cout<<"wi "<<var<<", "<<(_assignment[var]==AS_FALSE)<<" content:\n";
//      Stack<SATClause*>::Iterator wit2(_windex[wiIndex]);
//      while(wit2.hasNext()) {
//	cout<<(*wit2.next())<<endl;
//      }
//      cout<<endl;
//    }

    Stack<SATClause*>::Iterator wit(_windex[wiIndex]);
    while(wit.hasNext()) {
      SATClause* cl=wit.next();

      unsigned clen=cl->length();
      unsigned undefIndex=0;

      for(unsigned i=0;i<clen;i++) {
        SATLiteral lit=(*cl)[i];
        if(_assignment[lit.var()] == lit.polarity()) {
          //clause is true
          goto wit_cont;
        } else if(_assignment[lit.var()] == AS_UNDEFINED) {
          undefIndex=i;
        }
      }

      {
	//now we know that the clause is not true
	unsigned onlyUndefIndex;

	unsigned defWatchIndex=
	  (_assignment[(*cl)[0].var()]==AS_UNDEFINED) ? 1 : 0;
	ASS_NEQ(_assignment[(*cl)[defWatchIndex].var()], AS_UNDEFINED);

	unsigned undefWatchIndex=1-defWatchIndex;
	if(_assignment[(*cl)[undefWatchIndex].var()]!=AS_UNDEFINED) {
	  //both watched literals have become defined (and false)

//	  if(_assignmentLevels[(*cl)[1].var()]!=_level) {
//	    cout<<"var: "<<var<<endl;
//	    cout<<(*cl)<<endl;
//	    printAssignment();
//	  }

	  if(undefIndex==0) {
	    //the whole clause is false
	    ASS_REP(isFalse(cl), *cl);
	    return getBacktrackLevel(cl);
	  }
	  ASS_G(undefIndex,1);
	  unsigned undefIndex0=2;
	  while(undefIndex0<undefIndex && _assignment[ (*cl)[undefIndex0].var() ]!=AS_UNDEFINED)
	  {
	    undefIndex0++;
	  }
	  if(undefIndex0==undefIndex) {
	    //there is only one udefined literal
	    onlyUndefIndex=undefIndex;
	    goto literal_propagate;
	  }

	  //There are two undefined literals and we should make them watched.
	  //It means to unwatch the current ones...
	  unsigned otherWIIndex;
	  if( (*cl)[0].var()==var ) {
	    ASS_NEQ((*cl)[1].var(),var);
	    otherWIIndex=(*cl)[1].content();
	  } else {
	    ASS_EQ((*cl)[1].var(),var);
	    otherWIIndex=(*cl)[0].content();
	  }
	  wit.del();

	  Stack<SATClause*>::Iterator wit(_windex[otherWIIndex]);
#if VDEBUG
	  bool deleted=false;
#endif
	  while(wit.hasNext()) {
	    if(wit.next()==cl) {
	      wit.del();
#if VDEBUG
	      deleted=true;
#endif
	      break;
	    }
	  }
//	  if(!deleted) {
//	    Stack<SATClause*>::Iterator wit2(_windex[otherWIIndex]);
//	    cout<<"cl: "<<(*cl)<<endl;
//	    cout<<"windex "<<otherWIIndex<<endl;
//	    while(wit2.hasNext()) {
//	      cout<<(*wit2.next())<<endl;
//	    }
//	    cout<<endl;
//	  }
	  ASS(deleted);

	  //...and insert the new.
	  swap((*cl)[0], (*cl)[undefIndex0]);
	  swap((*cl)[1], (*cl)[undefIndex]);
	  insertIntoWatchIndex(cl);

	  continue;
	}

	//if we're here, we know that the clause is not true
	if(undefIndex>1) {
	  unsigned newWIIndex=(*cl)[undefIndex].content();
	  swap( (*cl)[defWatchIndex], (*cl)[undefIndex] );
	  wit.del();
	  _windex[newWIIndex].push(cl);
	  continue;
	}

	onlyUndefIndex=undefWatchIndex;
      literal_propagate:
	//Here we know that one literal is undefined and all others are false.
	//So let's unit-propagate...
	SATLiteral undefLit=(*cl)[onlyUndefIndex];
	unsigned uvar=undefLit.var();

	ASS_EQ(_assignment[uvar], AS_UNDEFINED);
	_assignment[uvar]=static_cast<AsgnVal>(undefLit.polarity());
	_assignmentLevels[uvar]=_level;
	_assignmentPremises[uvar]=cl;
	_unitStack.push(USRec(uvar, false));
	toDo.push(uvar);
      }

    wit_cont:;
    }
  }

  return _level;
}

void TWLSolver::addClauses(SATClauseIterator cit)
{
  CALL("TWLSolver::addClauses");

  LOG("");
  LOG("##############");

  if(_status==UNSATISFIABLE) {
    return;
  }

  try {
    while(cit.hasNext()) {
      SATClause* cl=cit.next();
      if(cl->length()==1) {
	addUnitClause(cl);
      } else {
	addClause(cl);
      }
    }

    int counter=0;

    unsigned chosenVar;
    while(chooseVar(chosenVar)) {
      _level++;
      _chosenVars[_level]=chosenVar;

      ASS_EQ(_assignment[chosenVar], AS_UNDEFINED);
      _assignment[chosenVar]=AS_TRUE;
      _assignmentLevels[chosenVar]=_level;
      _assignmentPremises[chosenVar]=0;
      _unitStack.push(USRec(chosenVar, true));

      LOG("choice point "<<chosenVar<<" to level "<<_level);

      unsigned propagatedVar=chosenVar;

      counter++;
      if(counter==50000) {
	counter=0;
	if(env.timeLimitReached()) {
	  throw TimeLimitExceededException();
	}
      }

    prop_loop:
      unsigned propBtLev=propagate(propagatedVar);
      if(propBtLev!=_level) {
      bt_loop:
	backtrack(propBtLev);

	if(_assignment[chosenVar]==AS_TRUE) {
	  //the true assignments follows from some clauses added later
	  //but we have shown that the true assignment leads to
	  //contradiction.

	  LOG("conflict on choice backtrack of var "<<chosenVar);

	  propBtLev=_level-1;
	  chosenVar=_chosenVars[_level];
	  goto bt_loop;
	}
	if(_assignment[chosenVar]==AS_UNDEFINED) {
	  LOG("choice negation of var "<<chosenVar<<" added at level "<<_level);
	  _assignment[chosenVar]=AS_FALSE;
	  _assignmentLevels[chosenVar]=_level;
	  _assignmentPremises[chosenVar]=0;
	  _unitStack.push(USRec(chosenVar, false));

	  propagatedVar=chosenVar;
	  chosenVar=_chosenVars[_level];
	  goto prop_loop;
	}

      }
//      printAssignment();
    }

  } catch (UnsatException e)
  {
    _status=UNSATISFIABLE;
    return;
  }

//  printAssignment();
}

bool TWLSolver::chooseVar(unsigned& var)
{
  CALL("TWLSolver::chooseVar");

  unsigned bestWCnt=0;
  unsigned bestWCntI=0;

  for(unsigned i=0;i<_varCnt;i++) {
    if(_assignment[i]!=AS_UNDEFINED) {
      continue;
    }
    unsigned wcnt=_windex[i*2].size() + _windex[i*2+1].size();
    if(wcnt>bestWCnt) {
//      var=i;
//      return true;
      bestWCnt=wcnt;
      bestWCntI=i;
    }
  }
  if(bestWCnt) {
    var=bestWCntI;
    return true;
  }
  return false;
}

void TWLSolver::addUnitClause(SATClause* cl)
{
  CALL("TWLSolver::addUnitClause");

  LOG("adding unit "<<(*cl));

  SATLiteral lit=(*cl)[0];
  unsigned lvar=lit.var();

  if(_assignment[lit.var()] == (1-lit.polarity())) {
    do {
      unsigned btLevel=getBacktrackLevel(cl);
      ASS_NEQ(btLevel, _level);
      backtrack(btLevel);
    } while (_assignment[lit.var()]!=AS_UNDEFINED);
  }
  ASS_NEQ(_assignment[lit.var()], (1-lit.polarity()));

  _assignmentLevels[lvar]=1;
  _assignmentPremises[lvar]=0;
  if( _assignment[lvar]==AS_UNDEFINED ) {
    _assignment[lvar]=static_cast<AsgnVal>(lit.polarity());
    _unitStack.push( USRec(lvar, false, true, true, 1) );

    unsigned propBtLev=propagate(lvar);
    backtrack(propBtLev);
  } else {
    _unitStack.push( USRec(lvar, false, true, false, 1) );
  }
}

void TWLSolver::addMissingWatchLitClause(SATClause* cl)
{
  CALL("TWLSolver::addMissingWatchLitClause");

  LOG("mwl clause: "<<(*cl));
//  printAssignment();
  LOG("--");

  SATLiteral wLit=(*cl)[0];
  SATLiteral swLit=(*cl)[1]; //second (pseudo-)watched literal

  unsigned wvar=wLit.var();

  ASS_NEQ(_assignment[swLit.var()], AS_UNDEFINED);

  unsigned lowerWatchLevel=_assignmentLevels[swLit.var()];
  ASS_L(lowerWatchLevel, _level);


//  if(_assignment[wvar]!=AS_UNDEFINED && _assignmentLevels[wvar]<=lowerWatchLevel) {
//    LOG("cl: "<<(*cl));
//    LOG("wvar: "<<wvar);
//    LOG("lowerWatchLevel: "<<lowerWatchLevel);
//    printAssignment();
//    LOG("");
//  }
  ASS(_assignment[wvar]==AS_UNDEFINED || _assignmentLevels[wvar]>lowerWatchLevel);

  _unprocessed[lowerWatchLevel].push(cl);

  _assignmentPremises[wvar]=cl;
  _assignmentLevels[wvar]=lowerWatchLevel;
  if( _assignment[wvar]==AS_UNDEFINED ) {
    _assignment[wvar]=static_cast<AsgnVal>(wLit.polarity());
    _unitStack.push( USRec(wvar, false, true, true, lowerWatchLevel) );

    unsigned propBtLev=propagate(wvar);
    backtrack(propBtLev);

  } else {
    _unitStack.push( USRec(wvar, false, true, false, lowerWatchLevel) );
  }
//  printAssignment();
  LOG("");
}


void TWLSolver::addClause(SATClause* cl)
{
  CALL("TWLSolver::addClause");

  LOG("adding clause "<<(*cl));

  unsigned clen=cl->length();
  ASS_G(clen,1);

  unsigned watched[2];
  unsigned wCnt=0;
  for(unsigned i=0;i<clen;i++) {
    SATLiteral lit=(*cl)[i];
    if(_assignment[lit.var()] != (1-lit.polarity())) {
      //literal is either true or undefined
      watched[wCnt]=i;
      wCnt++;
      if(wCnt==2) {
	break;
      }
    }
  }

  if(wCnt>=1) {
    swap( (*cl)[0], (*cl)[watched[0]] );
  }
  if(wCnt==2) {
    swap( (*cl)[1], (*cl)[watched[1]] );
  }

  if(wCnt==1) {
    SATLiteral wLit=(*cl)[0];
    unsigned wvar=wLit.var();

    unsigned hLevIndex=1;
    unsigned hLev=_assignmentLevels[ (*cl)[1].var() ];

    for(unsigned i=2;i<clen;i++) {
      SATLiteral lit=(*cl)[i];
      if(_assignmentLevels[lit.var()] > hLev) {
	hLevIndex=i;
	hLev=_assignmentLevels[lit.var()];
      }
    }
    swap( (*cl)[1], (*cl)[hLevIndex] );

    if(_assignment[wvar]!=AS_UNDEFINED && hLev>=_assignmentLevels[ wvar ]) {
      wCnt=2;
    } else if(_assignment[wvar]==AS_UNDEFINED && hLev==_level) {
      _assignment[wvar]=static_cast<AsgnVal>(wLit.polarity());
      _assignmentLevels[wvar]=_level;
      _assignmentPremises[wvar]=cl;
      _unitStack.push( USRec(wvar, false) );

      insertIntoWatchIndex(cl);
      unsigned propBtLev=propagate(wvar);
      backtrack(propBtLev);
      return;
    } else {
      addMissingWatchLitClause(cl);
      return;
    }

  }

  if(wCnt==2) {
    insertIntoWatchIndex(cl);
    return;
  }

  //the clause is false...
  ASS_EQ(wCnt,0);

  if(_assignmentLevels[ (*cl)[0].var() ] < _assignmentLevels[ (*cl)[1].var() ]) {
    swap( (*cl)[0], (*cl)[1] );
  }
  unsigned llvl=_assignmentLevels[ (*cl)[1].var() ]; //lower of the two highest levels
  for(unsigned i=2;i<clen;i++) {
    if(_assignmentLevels[ (*cl)[i].var() ] < llvl) {
      swap( (*cl)[1], (*cl)[i] );
      if(_assignmentLevels[ (*cl)[0].var() ] < _assignmentLevels[ (*cl)[1].var() ]) {
        swap( (*cl)[0], (*cl)[1] );
      }
      llvl=_assignmentLevels[ (*cl)[1].var() ];
    }
  }
  //the literal assigned at the highest level is at (*cl)[0], the next highest is (*cl)[1]

  //due to marked unit stack elements, one backtract might not be enough
  for(;;) {
    unsigned btLev=getBacktrackLevel(cl);
    ASS_NEQ(btLev, _level);
    backtrack(btLev);

    if(_assignment[(*cl)[0].var()]!=AS_UNDEFINED) {
      //some other literal could have become undefined
      for(unsigned i=1;i<clen;i++) {
        if(_assignment[ (*cl)[i].var() ] == AS_UNDEFINED) {
          swap( (*cl)[0], (*cl)[i] );
          break;
        }
      }
    }

    if(_assignment[(*cl)[0].var()]==AS_UNDEFINED) {
      break;
    }
  }

  if(_assignment[(*cl)[1].var()]!=AS_UNDEFINED) {
    //some other literal could have become undefined
    for(unsigned i=2;i<clen;i++) {
      if(_assignment[ (*cl)[i].var() ] == AS_UNDEFINED) {
        swap( (*cl)[1], (*cl)[i] );
        break;
      }
    }
  }

  if(_assignment[(*cl)[1].var()]==AS_UNDEFINED) {
    insertIntoWatchIndex(cl);
  } else {
    unsigned lvl1=_assignmentLevels[ (*cl)[1].var() ];
    for(unsigned i=2;i<clen;i++) {
      if(_assignmentLevels[ (*cl)[i].var() ] > lvl1) {
        swap( (*cl)[1], (*cl)[i] );
        lvl1=_assignmentLevels[ (*cl)[1].var() ];
      }
    }

    unsigned wvar=(*cl)[0].var();
    ASS_EQ(_assignment[wvar],AS_UNDEFINED);
    unsigned hLev=_assignmentLevels[ (*cl)[1].var() ];
    if(hLev==_level) {
      ASS_EQ(_assignment[wvar], AS_UNDEFINED);
      _assignment[wvar]=static_cast<AsgnVal>((*cl)[0].polarity());
      _assignmentLevels[wvar]=_level;
      _assignmentPremises[wvar]=cl;
      _unitStack.push( USRec(wvar, false) );

      insertIntoWatchIndex(cl);
      unsigned propBtLev=propagate(wvar);
      backtrack(propBtLev);
      return;
    }
    addMissingWatchLitClause(cl);
  }
}

void TWLSolver::insertIntoWatchIndex(SATClause* cl)
{
  _windex[(*cl)[0].content()].push(cl);
  _windex[(*cl)[1].content()].push(cl);
}

void TWLSolver::assertValid()
{
  CALL("TWLSolver::assertValid");

  for(unsigned i=0;i<_varCnt;i++) {
    if(_assignment[i]!=AS_UNDEFINED) {
      ASS_LE(_assignmentLevels[i],_level);
    }
  }

//  static bool vals[]={0,
//	  0, 0, 1, 1, 0, 0, 1, 0, 1, 0,
//	  1, 0, 1, 1, 0, 1, 0, 0, 0, 1,
//	  0, 1, 0, 0, 0, 0, 1, 0, 1, 0,
//	  0, 0, 0, 1, 0, 0, 0, 1, 1, 0,
//	  1, 1, 0, 0, 0, 0, 0, 0};
//
//  bool chosenMiss=false;

  Stack<USRec>::Iterator uit(_unitStack);
  while(uit.hasNext()) {
    USRec rec=uit.next();
    ASS_NEQ(_assignment[rec.var], AS_UNDEFINED);
    if(rec.mark) {
      ASS_LE(_assignmentLevels[rec.var], rec.markTgtLevel);
    }
//    if(rec.choice) {
//      if(!vals[rec.var]) {
//	chosenMiss=true;
//      }
//    }
  }
//  if(!chosenMiss) {
//    bool bad=false;
//    for(int i=1;i<=48;i++) {
//      if(_assignment[i]==(1-int(vals[i]))) {
//	LOG("bad value of "<<i<<": "<<_assignment[i]);
//	bad=true;
//      }
//    }
//    if(bad) {
//      printAssignment();
//      ASSERTION_VIOLATION;
//    }
//  }


//  if(reinterpret_cast<size_t>(_assignmentPremises[4])==0x691938) {
//    LOG("%% cl "<<(*_assignmentPremises[4]));
//  }
//  ASS_NEQ(reinterpret_cast<size_t>(_assignmentPremises[4]),0x691938);
}

bool TWLSolver::isFalse(SATClause* cl)
{
  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    if( _assignment[(*cl)[i].var()] != (1-(*cl)[i].polarity()) ) {
      return false;
    }
  }
  return true;
}

void TWLSolver::printAssignment()
{
  CALL("TWLSolver::printAssignment");

  for(unsigned i=0;i<_varCnt;i++) {
    if(_assignment[i]==AS_UNDEFINED) {
      cout<<i<<"\t"<<_assignment[i]<<endl;
    } else {
      cout<<i<<"\t"<<_assignment[i]<<"\t"<<_assignmentLevels[i];
      if(_assignmentPremises[i]) {
	cout<<"\t"<<(*_assignmentPremises[i])<<"\t"<<_assignmentPremises[i];
      }
      cout<<endl;
    }
  }
}

}
