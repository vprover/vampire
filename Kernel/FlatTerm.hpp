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
#include "Term.hpp"

namespace Kernel {

class FlatTerm
{
public:
  /**
   * Note: only allocates the flat term, but does not fill out its
   * content. The caller has to make sure @b Entry::expand is
   * called on each flat term entry before traversing its arguments.
   */
  static FlatTerm* create(TermList t);
  static FlatTerm* create(TermStack ts);
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
  static const unsigned ENTRY_TAG_BITS = 3;
  static_assert(FUN_UNEXPANDED < 1 << ENTRY_TAG_BITS, "EntryTag should fit within ENTRY_TAG_BITS");

  struct Entry
  {
    Entry() = default;
    Entry(EntryTag tag, unsigned num): _content(0) { _setTag(tag); _setNumber(num); }
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
    BITFIELD(64,
      BITFIELD_MEMBER(unsigned, _number, _setNumber, CHAR_BIT * sizeof(unsigned) - ENTRY_TAG_BITS,
      BITFIELD_MEMBER(unsigned, _tag, _setTag, ENTRY_TAG_BITS,
      END_BITFIELD
    )))
    BITFIELD_PTR_GET(Term, _term, 0)
    BITFIELD_PTR_SET(Term, _setTerm, 0)
    static_assert(sizeof(void *) <= sizeof(uint64_t), "must be able to fit a pointer into a 64-bit integer");
  };

  inline Entry& operator[](size_t i) { ASS_L(i,_length); return _data[i]; }
  inline const Entry& operator[](size_t i) const { ASS_L(i,_length); return _data[i]; }

  inline size_t size() const { return _length; }

  void swapCommutativePredicateArguments();
  void changeLiteralPolarity()
  { _data[0]._setNumber(_data[0]._number()^1); _data[1]._setTerm(Literal::complementaryLiteral(static_cast<Literal*>(_data[1]._term()))); }

private:
  template<bool mightBeLiteral>
  static size_t getEntryCount(Term* t);

  // pushes a term (as unexpanded if proper term) and adds its entry size to pos
  template<bool mightBeLiteral>
  static inline void pushTerm(Entry* e, size_t& pos, TermList t)
  {
    if (t.isVar()) {
      ASS(t.isOrdinaryVar());
      e[pos++] = Entry(VAR, t.var());
      return;
    }

    auto trm = t.term();
    if constexpr (mightBeLiteral) {
      e[pos] = Entry(FUN_UNEXPANDED, trm->isLiteral() ? static_cast<Literal*>(trm)->header() : trm->functor());
    } else {
      ASS(!trm->isLiteral());
      e[pos] = Entry(FUN_UNEXPANDED, trm->functor());
    }
    e[pos+1] = Entry(trm);
    e[pos+2] = Entry(FUN_RIGHT_OFS, getEntryCount<mightBeLiteral>(trm));
    pos += e[pos+2]._number();
  }

  FlatTerm(size_t length) : _length(length) {}
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