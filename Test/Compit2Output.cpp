
/*
 * File Compit2Output.cpp.
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
 * @file Compit2Output.cpp
 * Implements class Compit2Output for writing COMPIT benchmark files.
 */

#include "Compit2Output.hpp"

#if COMPIT_VERSION==2


#include <limits>
#include <ostream>

#include "Debug/Assertion.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"


namespace Test
{

using namespace std;
using namespace Kernel;

bool Compit2Output::signaturePrinted=false;

void Compit2Output::printSignature()
{
  CALL("Compit2Output::printSignature");
  ASS_L(env.signature->functions(), numeric_limits<WORD>::max());

  unsigned fCnt=env.signature->functions();
  WORD* buf=new WORD[2+fCnt];
  buf[0]=(WORD)fCnt;
  buf[1]=(WORD)fCnt;
  int pos=2;
  for(unsigned fn=0;fn<fCnt; fn++) {
    buf[pos++]=(WORD)env.signature->functionArity(fn);
  }
  cout.write(reinterpret_cast<char*>(buf),pos*sizeof(WORD));
  delete[] buf;

  signaturePrinted=true;
}

void Compit2Output::printSignatureForLiterals()
{
  CALL("Compit2Output::printSignature");
  ASS_L(env.signature->predicates()*2+env.signature->functions(), numeric_limits<WORD>::max());

  unsigned pCnt=env.signature->predicates();
  unsigned fCnt=env.signature->functions();
  unsigned symCnt=pCnt*2+fCnt;

  WORD* buf=new WORD[2+symCnt];
  buf[0]=(WORD)symCnt;
  buf[1]=(WORD)fCnt;
  int pos=2;
  for(unsigned fn=0;fn<fCnt; fn++) {
    buf[pos++]=(WORD)env.signature->functionArity(fn);
  }
  for(unsigned hdr=0;hdr<pCnt*2; hdr++) {
    buf[pos++]=(WORD)env.signature->predicateArity(hdr/2);
  }
  cout.write(reinterpret_cast<char*>(buf),pos*sizeof(WORD));
  delete[] buf;

  signaturePrinted=true;
}

WORD Compit2Output::getFunctorRepr(unsigned fn)
{
  CALL("Compit2Output::getFunctorRepr");
  return fn;
}

WORD Compit2Output::getPredSymbolRepr(unsigned header)
{
  CALL("Compit2Output::getPredSymbolRepr");
  return env.signature->functions()+header;
}

WORD Compit2Output::getVarRepr(unsigned var)
{
  CALL("Compit2Output::getVarRepr");
  ASS_G(-((int)var)-1, numeric_limits<WORD>::min());
  return -((int)var)-1;
}

size_t Compit2Output::requiredSize(TermList t)
{
  if(t.isOrdinaryVar()) {
    return 1;
  } else {
    ASS(t.isTerm());
    ASS(t.term()->shared());
    return t.term()->weight();
  }
}
size_t Compit2Output::requiredSize(Literal* lit)
{
  ASS(lit->shared());
  return lit->weight();
}

void Compit2Output::print(Operation op, TermList t, unsigned resultCount)
{
  CALL("Compit2Output::print(CompitOperation,TermList)");
  if(!signaturePrinted) {
    printSignature();
  }

  WORD* buf=new WORD[requiredSize(t)+2];

  switch(op) {
  case INSERT:
    buf[0]=-1;
    break;
  case DELETE:
    buf[0]=-2;
    break;
  case QUERY:
    ASS_L(resultCount, numeric_limits<WORD>::max());
    buf[0]=resultCount;
    break;
  }

  int pos=1;

  if(t.isOrdinaryVar()) {
    buf[pos++]=getVarRepr(t.var());
  } else {
    ASS(t.isTerm());
    Term::PolishSubtermIterator stit(t.term());
    while(stit.hasNext()) {
      TermList st=stit.next();
      if(st.isOrdinaryVar()) {
	buf[pos++]=getVarRepr(st.var());
      } else {
	ASS(st.isTerm());
	buf[pos++]=getFunctorRepr(st.term()->functor());
      }
    }
    buf[pos++]=getFunctorRepr(t.term()->functor());
  }
  buf[pos++]=TERM_SEPARATOR;

  cout.write(reinterpret_cast<char*>(buf),pos*sizeof(WORD));
  delete[] buf;
}

void Compit2Output::print(Operation op, Literal* lit, unsigned resultCount, bool complementary)
{
  CALL("Compit2Output::print(CompitOperation,Literal*)");
  if(!signaturePrinted) {
    printSignatureForLiterals();
  }

  WORD* buf=new WORD[requiredSize(lit)+2];

  switch(op) {
  case INSERT:
    buf[0]=-1;
    break;
  case DELETE:
    buf[0]=-2;
    break;
  case QUERY:
    ASS_L(resultCount, numeric_limits<WORD>::max());
    buf[0]=resultCount;
    break;
  }

  int pos=1;

  Term::PolishSubtermIterator stit(lit);
  while(stit.hasNext()) {
    TermList st=stit.next();
    if(st.isOrdinaryVar()) {
      buf[pos++]=getVarRepr(st.var());
    } else {
      ASS(st.isTerm());
      buf[pos++]=getFunctorRepr(st.term()->functor());
    }
  }
  buf[pos++]=getPredSymbolRepr(complementary?lit->complementaryHeader():lit->header());

  buf[pos++]=TERM_SEPARATOR;

  cout.write(reinterpret_cast<char*>(buf),pos*sizeof(WORD));
  delete[] buf;
}

void Compit2Output::fail()
{
  cout<<"\n## CANNOT CONVERT TO COMPIT ##\n";
  exit(0);
}

}

#endif
