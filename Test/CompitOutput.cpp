/**
 * @file CompitOutput.cpp
 * Implements class CompitOutput for writing COMPIT benchmark files.
 */

#include "../Debug/Assertion.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Environment.hpp"
#include "../Kernel/Signature.hpp"

#include "CompitOutput.hpp"

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

char CompitOutput::getFunctorChar(unsigned fn)
{
  CALL("CompitOutput::getFunctorChar");
  if(fn>158) {
    fail();
  }
  return 97+fn;
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

void CompitOutput::print(CompitOperation op, const TermList t)
{
  CALL("CompitOutput::print");
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

void CompitOutput::fail()
{
  cout<<"\n## CANNOT CONVERT TO COMPIT ##\n";
  exit(0);
}

}
