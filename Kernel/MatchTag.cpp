/**
 * @file MatchTag.cpp
 * Implements class MatchTag.
 */

#include "Term.hpp"

#include "MatchTag.hpp"

namespace Kernel
{

const int MatchTag::CONTENT_BITS;

size_t MatchTag::getContent(Term* t)
{
  unsigned arity=t->arity();
  if(arity==0) {
    return 0;
  }
  size_t res=0;
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
    size_t argContent;
    if(arg->isVar()) {
      argContent=~((size_t)0);
    } else {
      argContent=((size_t)arg->term()->functor()%31<<(CONTENT_BITS-5)) | (arg->term()->matchTag()._content>>5);
//      argContent=((size_t)arg->term()->functor()%15<<(CONTENT_BITS-4)) | (arg->term()->matchTag()._content>>4);
//      argContent=((size_t)arg->term()->functor()%7<<(CONTENT_BITS-3)) | (arg->term()->matchTag()._content>>3);
//      argContent=((size_t)arg->term()->functor()%3<<(CONTENT_BITS-2)) | (arg->term()->matchTag()._content>>2);
    }
    res=(res<<currBits) | (argContent>> (CONTENT_BITS-currBits));
    arg=arg->next();
  }
  return res;
}


}
