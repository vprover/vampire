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
 * @file SATClause.hpp
 * Defines class SATClause.
 */


#ifndef __SATClause__
#define __SATClause__

#include <iosfwd>

#include "Forwards.hpp"

#include "Lib/Metaiterators.hpp"
#include "Lib/Reflection.hpp"

#include "SATLiteral.hpp"

namespace SAT {

using namespace Lib;
using namespace Kernel;

/**
 * Class to represent clauses.
 * @since 10/05/2007 Manchester
 */
class SATClause
{
public:
  DECL_ELEMENT_TYPE(SATLiteral);

  auto iter() const { return arrayIter(*this); }

  /** New clause */
  SATClause(unsigned length);
  
  SATInference* inference() const { return _inference; }
  void setInference(SATInference* val);

  void* operator new(size_t,unsigned length);
  void operator delete(void *, size_t);

  unsigned defaultHash() const {
    unsigned hash = 0;
    for(unsigned i = 0; i < length(); i++)
      hash ^= DefaultHash::hash(_literals[i]);
    return hash;
  }

  bool operator==(const SATClause &other) const {
    if(length() != other.length())
      return false;
    for(unsigned i = 0; i < length(); i++)
      if(_literals[i] != other[i])
        return false;
    return true;
  }
  bool operator!=(const SATClause &other) const { return !operator==(other); }

  /**
   * Return the (reference to) the nth literal
   */
  inline SATLiteral& operator[] (int n)
  { return _literals[n]; }
  /** Return the (reference to) the nth literal */
  inline const SATLiteral& operator[] (int n) const
  { return const_cast<const SATLiteral&>(_literals[n]); }

  /** Return the length (number of literals) */
  inline unsigned length() const { return _length; }
  /** Alternative name for length to conform with other containers */
  inline unsigned size() const { return _length; }

  /** Return a pointer to the array of literals. */
  inline SATLiteral* literals() { return _literals; }

  /** True if the clause is empty */
  inline bool isEmpty() const { return _length == 0; }

  void sort();

  void destroy();

  std::string toString() const;

  static SATClause* removeDuplicateLiterals(SATClause *cl);

  static SATClause* fromStack(SATLiteralStack& stack);

private:
  /** number of literals */
  unsigned _length : 31;
  unsigned _nonDestroyable : 1;

  SATInference* _inference;


  /** Array of literals of this unit */
  SATLiteral _literals[1];
}; // class SATClause

std::ostream& operator<< (std::ostream& out, const SAT::SATClause& cl );

};

#endif /* __SATClause__ */
