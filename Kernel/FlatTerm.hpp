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
  static FlatTerm* create(Term* t);
  static FlatTerm* create(TermList t);
  static FlatTerm* create(TermStack ts);
  /**
   * Similar to @b create but only allocates the flat term,
   * and does not fill out its content. The caller has to
   * make sure @b expand is called on each flat term
   * entry before traversing its arguments.
   */
  static FlatTerm* createUnexpanded(Term* t);
  static FlatTerm* createUnexpanded(TermList t);
  static FlatTerm* createUnexpanded(TermStack ts);
  void destroy();

  static FlatTerm* copy(const FlatTerm* ft);

  inline const TermList& operator[](size_t i) const { ASS_L(i,_length); return _data[i]; }

  void swapCommutativePredicateArguments();
  void changeLiteralPolarity()
  {
    ASS(_data[0].isTerm() && _data[0].term()->isLiteral());
    _data[0].setTerm(Literal::complementaryLiteral(static_cast<Literal*>(_data[0].term())));
  }

  void expand(size_t i);

private:
  FlatTerm(size_t length);
  void* operator new(size_t,unsigned length);

  /**
   * The @b operator @b delete is undefined, FlatTerm objects should
   * be destroyed by the @b destroy() function
   */
  void operator delete(void*);

  size_t _length;
  TermList _data[1];
};

};

#endif /* __FlatTerm__ */
