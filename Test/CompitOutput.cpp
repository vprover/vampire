
/*
 * File CompitOutput.cpp.
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
 * @file CompitOutput.cpp
 * Implements class CompitOutput for writing COMPIT2 benchmark files.
 */

#include "CompitOutput.hpp"

#if COMPIT_VERSION==1

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

bool CompitOutput::signaturePrinted=false;

void CompitOutput::printSignature()
{
  CALL("CompitOutput::printSignature");
  unsigned fCnt=env.signature->functions();
  for(unsigned fn=0;fn<fCnt; fn++) {
    cout<<getFunctorChar(fn)<<'/'<<env.signature->functionArity(fn)<<'\n';
  }
  cout<<"$\n";
  signaturePrinted=true;
}

void CompitOutput::printSignatureForLiterals()
{
  CALL("CompitOutput::printSignatureForLiterals");
  unsigned fCnt=env.signature->functions();
  for(unsigned fn=0;fn<fCnt; fn++) {
    cout<<getFunctorChar(fn)<<'/'<<env.signature->functionArity(fn)<<'\n';
  }
  unsigned pCnt=env.signature->predicates();
  for(unsigned hdr=0;hdr<pCnt*2; hdr++) {
    cout<<getPredSymbolChar(hdr)<<'/'<<env.signature->predicateArity(hdr/2)<<'\n';
  }
  cout<<"$\n";
  signaturePrinted=true;
}

char CompitOutput::getFunctorChar(unsigned fn)
{
  CALL("CompitOutput::getFunctorChar");
  if(fn>158) {
    fail();
  }
  return 97+fn;
}

char CompitOutput::getPredSymbolChar(unsigned header)
{
  CALL("CompitOutput::getPredSymbolChar");
  unsigned index=env.signature->functions()+header;
  if(index>158) {
    fail();
  }
  return 97+index;
}

char CompitOutput::getVarChar(unsigned var)
{
  CALL("CompitOutput::getVarChar");
  if(var<10) {
    return 48+var;
  } else {
    if(var>35) {
      fail();
    }
    return 55+var;
  }
}

void CompitOutput::print(CompitOperation op, TermList t)
{
  CALL("CompitOutput::print(CompitOperation,TermList)");
  if(!signaturePrinted) {
    printSignature();
  }
  switch(op) {
  case INSERT:
    cout<<'+';
    break;
  case DELETE:
    cout<<'+';
    break;
  case SUCCESSFUL_QUERY:
    cout<<'!';
    break;
  case UNSUCCESSFUL_QUERY:
    cout<<'?';
    break;
  }
  if(t.isOrdinaryVar()) {
    cout<<getVarChar(t.var());
  } else {
    ASS(t.isTerm());
    cout<<getFunctorChar(t.term()->functor());
    Term::SubtermIterator stit(t.term());
    while(stit.hasNext()) {
      TermList st=stit.next();
      if(st.isOrdinaryVar()) {
	cout<<getVarChar(st.var());
      } else {
	ASS(st.isTerm());
	cout<<getFunctorChar(st.term()->functor());
      }
    }
  }
  cout<<'\n';
}

void CompitOutput::print(CompitOperation op, Literal* lit, bool complementary)
{
  CALL("CompitOutput::print(CompitOperation,Literal*)");
  if(!signaturePrinted) {
    printSignatureForLiterals();
  }
  switch(op) {
  case INSERT:
    cout<<'+';
    break;
  case DELETE:
    cout<<'+';
    break;
  case SUCCESSFUL_QUERY:
    cout<<'!';
    break;
  case UNSUCCESSFUL_QUERY:
    cout<<'?';
    break;
  }
  cout<<getPredSymbolChar(complementary?lit->complementaryHeader():lit->header());
  Term::SubtermIterator stit(lit);
  while(stit.hasNext()) {
    TermList st=stit.next();
    if(st.isOrdinaryVar()) {
      cout<<getVarChar(st.var());
    } else {
      ASS(st.isTerm());
      cout<<getFunctorChar(st.term()->functor());
    }
  }
  cout<<'\n';
}

void CompitOutput::fail()
{
  cout<<"\n## CANNOT CONVERT TO COMPIT ##\n";
  exit(0);
}

}

#endif
