
/*
 * File Substitution.hpp.
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
 * @file Substitution.hpp
 * Defines class Substitution.
 *
 * @since 08/07/2007 Manchester, flight Manchester-Cork
 * @since 30/12/2007 Manchester, reimplemented from scratch using a skip list
 * like structure
 */

#ifndef __Substitution__
#define __Substitution__

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/VString.hpp"

#include "Lib/Allocator.hpp"

#include "Signature.hpp"
#include "Term.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;


/* Class to facilitate higher-order prefix matching.
 * For example, if variable X in term X(a, b) is to be replaced 
 * by f c g(r) then an instance of prefix class would have f as 
 * functor and c g(r) as its prefix terms.
 */

class Prefix
{
public:
  //CLASS_NAME(Prefix);
  //USE_ALLOCATOR(Prefix);
 
  Prefix(){}
  Prefix(unsigned f, TermList* terms, unsigned length) : _argsLength(length), _functor(f)
  {
    if(!terms){
      _prefixArgs->makeEmpty();
    } else {
      _prefixArgs = terms;
    }
  }

  //Do prefixTerms require destroying in the destructor? AYB
  ~Prefix(){}

  TermList* prefixArgs() { return _prefixArgs; }
  unsigned functor() { return _functor; }
  unsigned prefixLength() { return _argsLength; }
 
#if VDEBUG
  vstring toString() const {
    CALL("Prefix::toString");
    bool first = true;
    vstring res;
   // if(_functor < )
    res = env.signature->getFunction(_functor)->name();
    res += "(";
    TermList* tl = _prefixArgs;
    while(tl->isNonEmpty()){  
      res += first ? tl->toString() : ", " + tl->toString();
      first = false;
      tl = tl->next();
    }
    res += "...";
    return res;
  }
#endif
private:
  unsigned _argsLength;
  unsigned _functor;
  TermList* _prefixArgs;
};

/**
 * The class Substitution implementing substitutions.
 * @since 30/12/2007 Manchester
 */
class Substitution
{
public:
  CLASS_NAME(Substitution);
  USE_ALLOCATOR(Substitution);
  DECLARE_PLACEMENT_NEW;

  Substitution() {}

  void bind(unsigned v,Term* t);
  void bind(unsigned v,TermList t);
  void bind(unsigned v, Prefix p);
  void rebind(unsigned v, Term* t);
  void rebind(unsigned v, TermList t);
  void rebind(unsigned v, Prefix p);
  bool findBinding(unsigned var, TermList& res) const;
  bool findBinding(unsigned var, Prefix& res) const;
  TermList apply(unsigned var);
  TermList applyHigherOrder(Term* varHeadTerm);
  void unbind(unsigned var);
  void reset();
  bool isEmpty() const { 
    return _map.isEmpty() && _hoLambdaMap.isEmpty() && _hoPrefixMap.isEmpty();
  }
#if VDEBUG
  vstring toString() const;
#endif
private:
  DHMap<unsigned,TermList> _map;
  /* maps a high-rder variable to a lambda term */
  DHMap<unsigned,TermList> _hoLambdaMap;
  /* maps a higher-order variable to a prefix */
  DHMap<unsigned,Prefix> _hoPrefixMap;

}; // class Substitution


}

#endif // __Substitution__

