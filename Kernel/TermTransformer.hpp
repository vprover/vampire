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
 * @file TermTransformer.hpp
 * Defines class TermTransformer.
 */

#ifndef __TermTransformer__
#define __TermTransformer__

#include "Forwards.hpp"
#include "Term.hpp"
#include "TypedTermList.hpp"


namespace Kernel {

/**
 * Class to allow for easy transformations of subterms in shared literals.
 *
 * The inheriting class implemets function transform(TermList)
 * and then the function transform(Literal*) uses it to transform subterms
 * of the given literal.
 *
 * The literal and subterms returned by the transform(TermList) function have
 * to be shared.
 *
 * This class can be used to transform sort arguments as well by suitably
 * implementing the transform(TermList) function
 * 
 * TermTransformer goes top down
 */
class TermTransformer {
public:
  TermTransformer() : 
    _sharedResult(true), 
    _dontTransformSorts(false) {}

  void createNonShared(){ _sharedResult = false; }
  void dontTransformSorts(){ _dontTransformSorts = true; }

  virtual ~TermTransformer() {}
  Term* transform(Term* term);
  Literal* transform(Literal* lit);
  TermList transform(TermList ts);

protected:
  virtual TermList transformSubterm(TermList trm) = 0;
  // Deliberately empty bodies. 
  // By default we do nothing on entry and exit
  virtual void onTermEntry(Term*){}
  virtual void onTermExit(Term*){}
  // default implementation explores all subterms when
  // a term has not been transformed (orig == new)
  // and none otherwise
  virtual bool exploreSubterms(TermList orig, TermList newTerm);
  Term* transformSpecial(Term* specialTerm);

  virtual Formula* transform(Formula* f);
  bool _sharedResult;
  bool _dontTransformSorts;

private:
  template<class T>
  Term* create(Term* t, TermList* argLst, bool shared)
  {  return shared ? T::create(static_cast<T*>(t), argLst) :  T::createNonShared(static_cast<T*>(t), argLst); }  
};

class SubtermReplacer : public TermTransformer {
public:
  SubtermReplacer(TermList what, TermList by
#if VHOL
    , bool liftFree = false
#endif
    ) : 
      _what(what) 
    , _by(by)
#if VHOL
    , _liftFreeIndices(liftFree)
    , _shiftBy(0)
#endif
  {
    ASS(what.isVar() || by.isVar() || SortHelper::getResultSort(what.term()) == SortHelper::getResultSort(by.term()));
    dontTransformSorts();
  }
      
  TermList transformSubterm(TermList t) override; 

#if VHOL
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override; 
#endif

private:
  TermList _what;
  TermList _by;
#if VHOL
  bool _liftFreeIndices; // true if need to lift free indices in _what
  int _shiftBy; // the amount to shift a free index by
#endif
};

class ToBank : public TermTransformer
{
public:
  ToBank(VarBank bank) : _bank(bank) {}

  Term*         toBank(Term* t){ return transform(t); }
  Literal*      toBank(Literal* l){ return transform(l); }  
  TypedTermList toBank(TypedTermList term);

  TermList transformSubterm(TermList t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;
private:
  VarBank _bank;
};


/**
 * Has similar philosophy to TermTransformer, but:
 *  goes bottom up and so subterms of currently considered terms
 *  might already be some replacements that happened earlier, e.g.:
 *  transforming g(f(a,b)) will consider (provided transformSubterm is the identity function)
 *  the following sequence: a,b,f(a,b),g(f(a,b)) 
 *  and if transformSubterm is the identitify everywhere except for f(a,b) for which it returns c,
 *  the considered sequence will be: a,b,f(a,b)->c,g(c)
 */
class BottomUpTermTransformer {
public:
  virtual ~BottomUpTermTransformer() {}
  Term* transform(Term* term);
  Literal* transform(Literal* lit);
protected:
  virtual TermList transformSubterm(TermList trm) = 0;
  /**
   * TODO: these functions are similar as in TermTransformer, code duplication could be removed
   */
  TermList transform(TermList ts);
  Formula* transform(Formula* f);
};

}

#endif // __TermTransformer__
