/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __TERM_ALGEBRA__
#define __TERM_ALGEBRA__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/List.hpp"
#include "Lib/Array.hpp"
#include "Lib/VString.hpp"
#include "Kernel/OperatorType.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Set.hpp"

using Kernel::TermList;

namespace Shell {
  class TermAlgebraConstructor {
  public:
    CLASS_NAME(TermAlgebraConstructor);
    USE_ALLOCATOR(TermAlgebraConstructor);

    /* A term algebra constructor, described by its name, range,
       arity, and for each argument: the name of its destructor and
       its sort*/
    TermAlgebraConstructor(unsigned functor, Lib::Array<unsigned> destructors);
    TermAlgebraConstructor(unsigned functor, std::initializer_list<unsigned> destructors);
    TermAlgebraConstructor(unsigned functor, unsigned discriminator, Lib::Array<unsigned> destructors);
    ~TermAlgebraConstructor() {}

    unsigned arity() const;
    unsigned numTypeArguments() const;
    TermList argSort(unsigned ith) const;
    TermList rangeSort() const;

    /* True iff one of the arguments has the same sort as the range */
    bool recursive();

    /* The numbers of the constructor and destructors functions in the
       environment signature. These functions should be called only
       after createSymbols() has been called once */
    unsigned functor() const { return _functor; }
    unsigned destructorFunctor(unsigned ith) { return _destructors[ith]; }

    bool hasDiscriminator() { return _hasDiscriminator; }
    unsigned discriminator();
 
    class IterArgSorts 
    {
      TermAlgebraConstructor& _self;
      unsigned _idx;
    public:
      DECL_ELEMENT_TYPE(TermList);

      IterArgSorts(TermAlgebraConstructor& ta) : _self(ta), _idx(0) {}

      bool hasNext() const 
      { return _idx < _self.arity(); }

      auto next() 
      { return _self.argSort(_idx++); }
    };

    Lib::IterTraits<IterArgSorts> iterArgSorts()
    { return Lib::iterTraits(IterArgSorts(*this)); }

   
    friend std::ostream& operator<<(std::ostream& out, TermAlgebraConstructor const& self);
  private:
    Lib::vstring discriminatorName();

    Kernel::OperatorType* _type;
    unsigned _functor;
    bool _hasDiscriminator;
    unsigned _discriminator;
    Lib::Array<unsigned> _destructors;
  };

  typedef Lib::Array<TermAlgebraConstructor*> ConstructorArray;

  class TermAlgebra {
  public:
    CLASS_NAME(TermAlgebra);
    USE_ALLOCATOR(TermAlgebra);


    /* An algebra described by its name, sort, number of constructors,
       the constructors themselves (whose range must be the algebra
       sort), and their cyclicity. If allowsCyclicTerms is false, and
       the option -tar is not set to off, then the acyclicity rule
       will be enforced for terms of this algebra*/
    TermAlgebra(TermList sort,
                unsigned n,
                TermAlgebraConstructor** constrs,
                bool allowsCyclicTerms = false);
    TermAlgebra(TermList sort,
                Lib::Array<TermAlgebraConstructor*> constrs,
                bool allowsCyclicTerms = false);
    TermAlgebra(TermList sort,
                std::initializer_list<TermAlgebraConstructor*> constrs,
                bool allowsCyclicTerms = false);
    ~TermAlgebra() {}

    unsigned nTypeArgs() const { return _sort.term()->arity(); }
    unsigned nConstructors() const { return _n; }
    TermList sort() const { return _sort; }
    TermAlgebraConstructor* constructor(unsigned ith) { ASS_L(ith, _n); return _constrs[ith]; }

    class IterCons 
    {
      TermAlgebra& _ta;
      unsigned _idx;
    public:
      DECL_ELEMENT_TYPE(TermAlgebraConstructor*);

      IterCons(TermAlgebra& ta) : _ta(ta), _idx(0) {}

      bool hasNext() const 
      { return _idx < _ta.nConstructors(); }

      TermAlgebraConstructor* next() 
      { return _ta.constructor(_idx++); }
    };

    Lib::IterTraits<IterCons> iterCons()
    { return Lib::iterTraits(IterCons(*this)); }


    /** returns all sorts contained in the term algebra instance `sort`, including `sort` itself.
     * consider for example:
     *  nat      ::= S(nat)                           | Zero
     *  atree(x) ::= Node(atree(x), x, nat, atree(x)) | Leaf
     *  intp     ::= P(int,int)
     *
     * then subSorts(atree(intp)) == { int, nat, intp, atree(intp) }
     */
    static Lib::Set<TermList> subSorts(TermList sort);

    bool allowsCyclicTerms() { return _allowsCyclicTerms; }

    /* True iff the algebra defines an empty domain, which could be
       due to:
       - having no constructors
       - not allowing cyclic terms and having only recursive constructors
     */
    bool emptyDomain();

    /* True iff all the constructors are constants */
    bool finiteDomain();
    /* True iff one of the constructors is recursive */
    bool infiniteDomain();

    /* The predicate of the subterm relation, used only if the option
       -tac is set to "axiom"*/
    Lib::vstring getSubtermPredicateName();
    unsigned getSubtermPredicate();
    void getTypeSub(Kernel::Term* t, Kernel::Substitution& subst);

    friend std::ostream& operator<<(std::ostream& out, TermAlgebra const& self);
  private:
    TermList _sort;
    unsigned _n; /* number of constructors */
    bool _allowsCyclicTerms;
    ConstructorArray _constrs;
  };
}

#endif

