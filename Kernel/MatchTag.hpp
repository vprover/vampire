/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file MatchTag.hpp
 * Defines class MatchTag.
 */


#ifndef __MatchTag__
#define __MatchTag__

#include "Forwards.hpp"

#include "Lib/BitUtils.hpp"

//Tests shown it as not helping. Perhaps needs just some improvement of bit selection.
#define USE_MATCH_TAG 0

namespace Kernel {

#if USE_MATCH_TAG


class MatchTag
{
public:
  inline void makeEmpty() throw() {_content=EMPTY_CONTENT; }

  inline bool isEmpty() {
    return _content==EMPTY_CONTENT;
  }

  inline void ensureInit(Term* t)
  {
    if(isEmpty()) {
      init(t);
    }
  }

  inline bool couldBeInstanceOf(MatchTag base)
  {
    if(base._content==EMPTY_CONTENT_REPLACEMENT) {
      return BitUtils::isSubset(EMPTY_CONTENT, _content);
    }
    return BitUtils::isSubset(base._content, _content);
  }
  inline bool couldBeInstanceOfReversed(MatchTag base)
  {
    if(base._content==EMPTY_CONTENT_REPLACEMENT) {
      return BitUtils::isSubset(EMPTY_CONTENT, _highContent) &&
        BitUtils::isSubset(base._highContent, _lowContent);
    }
    return BitUtils::isSubset(base._lowContent, _highContent) &&
      BitUtils::isSubset(base._highContent, _lowContent);
  }


  static const unsigned EMPTY_CONTENT=3;
  static const unsigned EMPTY_CONTENT_REPLACEMENT=1;
  static const unsigned CONTENT_BITS=sizeof(unsigned)*8;

private:
  void init(Term* t);

  static unsigned getContent(Term* t);

  union {
    unsigned _content;
    struct {
      unsigned _lowContent : CONTENT_BITS/2;
      unsigned _highContent : CONTENT_BITS/2;
    };
  };
};

static_assert(
  (MatchTag::EMPTY_CONTENT & MatchTag::EMPTY_CONTENT_REPLACEMENT)==MatchTag::EMPTY_CONTENT_REPLACEMENT,
  "EMPTY_CONTENT_REPLACEMENT is subset of EMPTY_CONTENT"
);
static_assert(
  MatchTag::EMPTY_CONTENT < 0x10000,
  "EMPTY_CONTENT_REPLACEMENT has zeroes only in the lower half"
);

#endif

};

#endif /* __MatchTag__ */
