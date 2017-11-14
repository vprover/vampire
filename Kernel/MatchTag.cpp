
/*
 * File MatchTag.cpp.
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
 * @file MatchTag.cpp
 * Implements class MatchTag.
 */

#include "Lib/Int.hpp"
#include "Term.hpp"

#include "MatchTag.hpp"

namespace Kernel
{

#if USE_MATCH_TAG

const unsigned MatchTag::EMPTY_CONTENT;
const unsigned MatchTag::EMPTY_CONTENT_REPLACEMENT;
const unsigned MatchTag::CONTENT_BITS;

void MatchTag::init(Term* t) {
  ASS(t->shared());

  static Stack<TermList*> stack(32);
  static Stack<Term*> terms(32);

  terms.push(t);
  stack.push(t->args());
  TermList* tt;
  while(!stack.isEmpty()) {
    tt=stack.pop();
    if(tt->isEmpty()) {
      Term* t=terms.pop();
      t->matchTag()._content=getContent(t);
      continue;
    }
    stack.push(tt->next());
    if(tt->isTerm() && tt->term()->matchTag().isEmpty()) {
      Term* t=tt->term();
      terms.push(t);
      stack.push(t->args());
    }
  }
  ASS(!isEmpty());
}

unsigned MatchTag::getContent(Term* t)
{
  CALL("MatchTag::getContent");

  unsigned arity=t->arity();
  if(arity==0) {
    return 0;
  }
  unsigned res=0;
  unsigned currOfs=0;
  unsigned bitsPerArg=CONTENT_BITS/arity;
  unsigned largerArgs=CONTENT_BITS%arity;
  TermList* arg=t->args();
  while(arg->isNonEmpty()) {
    unsigned currBits;
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
      unsigned argArity=arg->term()->arity();
      unsigned argFunctor=arg->term()->functor();

      if(argArity) {
	fnBits=min( BitUtils::log2(argFunctor)/2+1 ,currBits);
//	fnBits=min( 4u ,currBits);
//	fnBits=min( (argFunctor>64u) ? 5u : 3u ,currBits);
	paramBits=currBits-fnBits;
      } else {
	fnBits=currBits;
	paramBits=0;
      }
      if(paramBits) {
	ASS(!arg->term()->matchTag().isEmpty());
	unsigned in=arg->term()->matchTag()._content;
	if(argArity==1) {
	  argContent=in;
	} else if(argArity==2) {
	  unsigned pbHalf=paramBits/2;
	  unsigned pbMask=(1<<(pbHalf))-1;
	  argContent=in&pbMask && in>>(CONTENT_BITS/2-pbHalf);

	} else {
	  argContent=0;
	  unsigned step=CONTENT_BITS/paramBits;
	  unsigned remPb=paramBits;
	  while(remPb) {
	    argContent = (argContent<<1) | (in&1);
	    in>>=step;
	    remPb--;
	  }
	}


      } else {
	argContent=0;
      }
      unsigned fnModulo= (fnBits==CONTENT_BITS) ? (~0u) : ((1<<fnBits)-1);
      argContent=(argContent<<fnBits) && (argFunctor%fnModulo);
    }
    unsigned mask=(1<<currBits)-1;
//    res=(res<<currBits) | (argContent&mask);
    res|=(argContent&mask)<<currOfs;
    currOfs+=currBits;
    arg=arg->next();
  }
  if(res==EMPTY_CONTENT) {
    res=EMPTY_CONTENT_REPLACEMENT;
  }
  return res;
}

#endif

}
