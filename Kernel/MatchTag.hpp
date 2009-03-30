/**
 * @file MatchTag.hpp
 * Defines class MatchTag.
 */


#ifndef __MatchTag__
#define __MatchTag__

#include "../Forwards.hpp"

#include "../Lib/BitUtils.hpp"

#define USE_MATCH_TAG 1

namespace Kernel {

#if USE_MATCH_TAG


class MatchTag
{
public:
  inline void makeEmpty() {_content=EMPTY_CONTENT; }

  inline bool isEmpty() {
    return _content==EMPTY_CONTENT;
  }

  inline void ensureInit(Term* t)
  {
    ASS(t->shared());
    if(isEmpty()) {
      init(t);
    }
  }

  inline bool couldBeInstanceOf(MatchTag inst)
  { return BitUtils::isSubset(inst._content, _content); }
  inline bool couldBeInstanceOfReversed(MatchTag inst)
  {
    return BitUtils::isSubset(inst._lowContent, _highContent) &&
      BitUtils::isSubset(inst._highContent, _lowContent);
  }

private:
  void init(Term* t);

  static unsigned getContent(Term* t);
  static const unsigned EMPTY_CONTENT=0;
  static const unsigned CONTENT_BITS=sizeof(unsigned)*8;

  union {
    unsigned _content;
    struct {
      unsigned _lowContent : CONTENT_BITS/2;
      unsigned _highContent : CONTENT_BITS/2;
    };
  };
};

#endif

};

#endif /* __MatchTag__ */
