#ifndef __TERM_ALGEBRA__
#define __TERM_ALGEBRA__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/List.hpp"
#include "Lib/Array.hpp"
#include "Lib/VString.hpp"

namespace Shell {
  class TermAlgebraConstructor {
  public:
    CLASS_NAME(TermAlgebraConstructor);
    USE_ALLOCATOR(TermAlgebraConstructor);

    /* A term algebra constructor, described by its name, range,
       arity, and for each argument: the name of its destructor and
       its sort*/
    TermAlgebraConstructor(unsigned functor, Lib::Array<unsigned> destructorFunctors);
    ~TermAlgebraConstructor() {}

    unsigned arity();
    unsigned argSort(unsigned ith);
    unsigned rangeSort();

    /* True iff one of the arguments has the same sort as the range */
    bool recursive();

    /* The numbers of the constructor and destructors functions in the
       environment signature. These functions should be called only
       after createSymbols() has been called once */
    unsigned functor() {return _functor; }
    unsigned destructorFunctor(unsigned ith) { return _destructorFunctors[ith]; }

    /* Subterm definitions used by the acyclicity axiom. True iff some
       definition was actually added (i.e. if the constructor is
       recursive) */
    bool addSubtermDefinitions(unsigned subtermPredicate, Kernel::UnitList*& units);

  private:
    unsigned _functor;
    Kernel::FunctionType* _type;
    Lib::Array<unsigned> _destructorFunctors;
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
    TermAlgebra(Lib::vstring name,
                unsigned sort,
                unsigned n,
                TermAlgebraConstructor** constrs,
                bool allowsCyclicTerms = false);
    ~TermAlgebra() {}

    Lib::vstring name() { return _tname; }
    unsigned sort() { return _sort; }
    unsigned nConstructors() { return _n; }
    TermAlgebraConstructor* constructor(unsigned ith) { ASS_L(ith, _n); return _constrs[ith]; }
    bool allowsCyclicTerms() { return _allowsCyclicTerms; }

    /* True iff the algebra defines an empty domain, which could be
       due to:
       - having no constructors
       - not allowing cyclic terms and having only recursive constructors
     */
    bool emptyDomain();

    /* The predicate of the subterm relation, used only if the option
       -tac is set to "axiom"*/
    Lib::vstring getSubtermPredicateName() { return "subterm$" + _tname; }
    unsigned getSubtermPredicate();

    /* Theory axioms */
    void addExhaustivenessAxiom(Kernel::UnitList*& units);
    void addDistinctnessAxiom(Kernel::UnitList*& units);
    void addInjectivityAxiom(Kernel::UnitList*& units);
    void addAcyclicityAxiom(Kernel::UnitList*& units);
  private:
      Lib::vstring _tname;
    unsigned _n; /* number of constructors */
    ConstructorArray _constrs;
    unsigned _sort;
    bool _allowsCyclicTerms;
  };

}

#endif
