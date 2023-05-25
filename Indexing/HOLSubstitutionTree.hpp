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
 * @file TermSubstitutionTree.hpp
 * Defines class TermSubstitutionTree.
 */


#ifndef __HOLSubstitutionTree__
#define __HOLSubstitutionTree__

#if VHOL


#include "Forwards.hpp"
#include "SubstitutionTree.hpp"

#include "Kernel/Renaming.hpp"
#include "Kernel/ApplicativeHelper.hpp"

namespace Indexing {

/** A variant of substitution tree that supports non-splitting nodes */
class HOLSubstitutionTree
: public SubstitutionTree
{
  using SplittableType = std::function<bool(TermList)>;

public:
  CLASS_NAME(HOLSubstitutionTree);
  USE_ALLOCATOR(HOLSubstitutionTree);

  HOLSubstitutionTree(SplittableType f) : SubstitutionTree(), _splittable(f) {}

  class Subterm {
    TermList _subterm;
    bool _splittable;
  public: 
    Subterm(TermList t, bool splittable)
    : _subterm(t), _splittable(splittable) {}

    // dummy constructor needed for use in DHMap
    Subterm(){}

    bool splittable() const {  return _splittable; }

    TermList::Top top(){
      return _subterm.top(_splittable);
    }

    TermList term() const { return _subterm; }
    TermList* termPtr() { return &_subterm; }

    friend std::ostream& operator<<(std::ostream& out, Subterm const& self);
  };


private:
  class SubtermPair
  {
    TermList* _t1;
    TermList* _t2;
    bool _t1Splittable;
    bool _t2Splittable;
  public:
    SubtermPair(TermList* t1, bool t1s, TermList* t2, bool t2s)
    : _t1(t1),  _t2(t2), _t1Splittable(t1s), _t2Splittable(t2s) {}

    TermList* lhs() { return _t1; }
    TermList* rhs() { return _t2; }

    bool lhsSplittable() { return _t1Splittable; }
    bool rhsSplittable() { return _t2Splittable; }

    TermList::Top lhsTop() { return _t1->top(_t1Splittable); }
    TermList::Top rhsTop() { return _t2->top(_t2Splittable); }    
  };

  typedef DHMap<unsigned,Subterm,IdentityHash,DefaultHash> HOLBindingMap;
  typedef ApplicativeHelper AH;

  SplittableType _splittable;

public:


  void handle(TypedTermList const& key, LeafData ld, bool doInsert) override
  { handleImplHol(key, ld, doInsert); }

  void handle(Literal* const& key, LeafData ld, bool doInsert) override
  { handleImplHol(key, ld, doInsert); }

  template<class Key>
  void handleImplHol (Key const& key, LeafData ld, bool doInsert)
  {
    auto norm = Renaming::normalize(key,VarBank::NORM_RESULT_BANK);
    Recycled<HOLBindingMap> bindings;
    setSort(key, ld);
    createHOLBindings(norm, /* reversed */ false,
        [&](auto var, auto term) { 
          bindings->insert(var, term);
          _nextVar = max(_nextVar, (int)var + 1);
        });
    if (doInsert) higherOrderInsert(*bindings, ld);
    else          higherOrderRemove(*bindings, ld);
  }
 
  void higherOrderInsert(HOLBindingMap& binding,LeafData ld);
  void higherOrderRemove(HOLBindingMap& binding,LeafData ld);

  // TODO document
  template<class BindingFunction>
  void createHOLBindings(TypedTermList term, bool reversed, BindingFunction bindSpecialVar)
  {
    bindSpecialVar(0, Subterm(term, _splittable(term)));
    bindSpecialVar(1, Subterm(term.sort(),true));
  }

  template<class BindingFunction>
  void createHOLBindings(Literal* lit, bool reversed, BindingFunction bindSpecialVar)
  {
    // equality is the only predicate
    ASS(lit->isEquality());

    TermList l0 = *lit->nthArgument(0);
    TermList l1 = *lit->nthArgument(1);

    if (reversed) {
      bindSpecialVar(1,Subterm(l0, _splittable(l0)) );
      bindSpecialVar(0,Subterm(l1, _splittable(l1)) );
    } else {
      bindSpecialVar(0,Subterm(l0, _splittable(l0)) );
      bindSpecialVar(1,Subterm(l1, _splittable(l1)) );
    }

    auto sort = SortHelper::getEqualityArgumentSort(lit);
    bindSpecialVar(2, Subterm(sort, true));
  }

};

};

#endif

#endif /* __TermSubstitutionTree__ */
