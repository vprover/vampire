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
  void init(Term* t) {
    _content=getContent(t);
  }

  inline bool couldBeInstanceOf(MatchTag inst)
  { return BitUtils::isSubset(inst._content, _content); }
  inline bool couldBeInstanceOfReversed(MatchTag inst)
  {
    return BitUtils::isSubset(inst._lowContent, _highContent) &&
      BitUtils::isSubset(inst._highContent, _lowContent);
  }

private:

  static unsigned getContent(Term* t);
  static const int CONTENT_BITS=sizeof(unsigned)*8;

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
