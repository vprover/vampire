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
 * @file FlatTerm.hpp

 * Defines class FlatTerm.
 */

#ifndef __FlatTerm__
#define __FlatTerm__

#include "Forwards.hpp"

namespace Kernel {

class FlatTerm
{
public:
  static FlatTerm* create(Term* t);
  static FlatTerm* create(TermList t);
  /**
   * Similar to @b create but only allocates the flat term,
   * and does not fill out its content. The caller has to
   * make sure @b Entry::expand is called on each flat term
   * entry before traversing its arguments.
   */
  static FlatTerm* createUnexpanded(Term* t);
  static FlatTerm* createUnexpanded(TermList t);
  void destroy();

  static FlatTerm* copy(const FlatTerm* ft);

  static constexpr size_t FUNCTION_ENTRY_COUNT=3;

  enum EntryTag {
    FUN_TERM_PTR = 0,
    FUN = 1,
    VAR = 2,
    /**
     * If tag is set to this, @b number() gives offset that needs to be
     * added to the position of the corresponding @b FUN Entry in order
     * to get behind the function
     */
    FUN_RIGHT_OFS = 3,
    FUN_UNEXPANDED = 4,
  };

  struct Entry
  {
    Entry() = default;
    Entry(EntryTag tag, unsigned num) { _setTag(tag); _setNumber(num); }
    Entry(Term* term) { _setTerm(term); ASS_EQ(_tag(), FUN_TERM_PTR); }

    inline bool isVar() const { return _tag()==VAR; }
    inline bool isVar(unsigned num) const { return isVar() && _number()==num; }
    inline bool isFun() const { return _tag()==FUN || _tag()==FUN_UNEXPANDED; }
    inline bool isFun(unsigned num) const { return isFun() && _number()==num; }
    /**
     * Should be called when @b isFun() is true.
     * If @b tag()==FUN_UNEXPANDED, it fills out entries for the functions
     * arguments with FUN_UNEXPANDED values. Otherwise does nothing.
     */
    void expand();

    uint64_t _content;

    static constexpr unsigned
      TAG_BITS_START = 0,
      TAG_BITS_END = TAG_BITS_START + 3,
      NUMBER_BITS_START = TAG_BITS_END,
      NUMBER_BITS_END = NUMBER_BITS_START + 27,
      TERM_BITS_START = 0,
      TERM_BITS_END = CHAR_BIT * sizeof(Term *);

    // various properties we want to check
    static_assert(TAG_BITS_START == 0, "tag must be the least significant bits");
    static_assert(TERM_BITS_START == 0, "term must be the least significant bits");
    static_assert(sizeof(void *) <= sizeof(uint64_t), "must be able to fit a pointer into a 64-bit integer");
    static_assert(FUN_UNEXPANDED < 8, "must be able to squash orderings into 3 bits");

  // getters and setters
#define GET_AND_SET(type, name, Name, NAME) \
    type _##name() const { return BitUtils::getBits<NAME##_BITS_START, NAME##_BITS_END>(*this); }\
    void _set##Name(type val) { BitUtils::setBits<NAME##_BITS_START, NAME##_BITS_END>(*this, val); }
    GET_AND_SET(unsigned, tag, Tag, TAG)
    GET_AND_SET(unsigned, number, Number, NUMBER)
#undef GET_AND_SET
    Term *_term() const
    { return reinterpret_cast<Term *>(BitUtils::getBits<TERM_BITS_START, TERM_BITS_END>(*this)); }
    void _setTerm(Term *term)
    { BitUtils::setBits<TERM_BITS_START, TERM_BITS_END>(*this, reinterpret_cast<uint64_t>(term)); }
    // end bitfield
  };

  inline Entry& operator[](size_t i) { ASS_L(i,_length); return _data[i]; }
  inline const Entry& operator[](size_t i) const { ASS_L(i,_length); return _data[i]; }

  void swapCommutativePredicateArguments();
  void changeLiteralPolarity()
  { _data[0]._setNumber(_data[0]._number()^1); }

private:
  static size_t getEntryCount(Term* t);

  FlatTerm(size_t length);
  void* operator new(size_t,unsigned length);

  /**
   * The @b operator @b delete is undefined, FlatTerm objects should
   * be destroyed by the @b destroy() function
   */
  void operator delete(void*);

  size_t _length;
  Entry _data[1];
};

};

#endif /* __FlatTerm__ */
