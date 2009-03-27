/**
 * @file MatchTag.cpp
 * Implements class MatchTag.
 */

#include "../Lib/Int.hpp"
#include "Term.hpp"

#include "MatchTag.hpp"

namespace Kernel
{

#if USE_MATCH_TAG

const int MatchTag::CONTENT_BITS;

unsigned MatchTag::getContent(Term* t)
{
  unsigned arity=t->arity();
  if(arity==0) {
    return 0;
  }
  unsigned res=0;
  int bitsPerArg=CONTENT_BITS/arity;
  int largerArgs=CONTENT_BITS%arity;
  TermList* arg=t->args();
  while(arg->isNonEmpty()) {
    int currBits;
    if(largerArgs) {
      largerArgs--;
      currBits=bitsPerArg+1;
    } else {
      currBits=bitsPerArg;
    }
    if(currBits==0) {
      break;
    }
    unsigned argContent;
    if(arg->isVar()) {
      argContent=~((unsigned)0);
    } else {
      unsigned fnBits;
      unsigned paramBits;

      if(arg->term()->arity()) {
	fnBits=min(4,currBits);
	paramBits=currBits-fnBits;
      } else {
	fnBits=currBits;
	paramBits=0;
      }
      unsigned fnModulo= (fnBits==CONTENT_BITS) ? (~0u) : ((1<<fnBits)-1);
      if(paramBits) {
	unsigned in=arg->term()->matchTag()._content;
//	unsigned out=0;
//	unsigned step=CONTENT_BITS/paramBits;
//	while(paramBits) {
//	  out = (out<<1) | (in&1);
//	  in>>=step;
//	  paramBits--;
//	}
//
//	argContent=out<<fnBits;
	argContent=in;
      } else {
	argContent=0;
      }
      argContent=(argContent<<fnBits) && (arg->term()->functor()%fnModulo);
    }
    unsigned mask=(1<<currBits)-1;
    res=(res<<currBits) | (argContent&mask);
    arg=arg->next();
  }
  return res;
}

#endif

}
