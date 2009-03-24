/**
 * @file MatchTag.hpp
 * Defines class MatchTag.
 */


#ifndef __MatchTag__
#define __MatchTag__

#include "../Forwards.hpp"

#include "../Lib/BitUtils.hpp"

namespace Kernel {

class MatchTag
{
public:
  void init(Term* t) {
    _content=getContent(t);
  }

  bool couldBeInstanceOf(MatchTag inst)
  { return BitUtils::isSubset(inst._content, _content); }
  bool couldBeInstanceOfReversed(MatchTag inst)
  {
    return BitUtils::isSubset(inst._lowContent, _highContent) &&
      BitUtils::isSubset(inst._highContent, _lowContent);
  }

private:

  static size_t getContent(Term* t);
  static const int CONTENT_BITS=sizeof(size_t)*8;

  union {
    size_t _content;
    struct {
      unsigned _lowContent : CONTENT_BITS/2;
      unsigned _highContent : CONTENT_BITS/2;
    };
  };
};

};

#endif /* __MatchTag__ */
