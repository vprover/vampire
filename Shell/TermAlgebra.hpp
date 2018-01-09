
/*
 * File TermAlgebra.hpp.
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
#ifndef __TERM_ALGEBRA__
#define __TERM_ALGEBRA__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Array.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Map.hpp"
#include "Lib/Set.hpp"
#include "Lib/VString.hpp"

#include "Kernel/Sorts.hpp"

namespace Shell {

  class TermAlgebra;
  
  class TermAlgebraConstructor {
  public:
    CLASS_NAME(TermAlgebraConstructor);
    USE_ALLOCATOR(TermAlgebraConstructor);

    /* A term algebra constructor, described by its name, range,
       arity, and for each argument: the name of its destructor and
       its sort*/
    TermAlgebraConstructor(unsigned functor, Lib::Array<unsigned> destructors);
    TermAlgebraConstructor(unsigned functor, unsigned discriminator, Lib::Array<unsigned> destructors);
    ~TermAlgebraConstructor() {}

    unsigned arity() { return _type->arity(); }
    unsigned argSort(unsigned ith) { return _type->arg(ith); }
    unsigned rangeSort() { return _type->result(); }
    Lib::vstring name();

    /* True iff one of the arguments has the same sort as the range */
    bool recursive();

    /* The numbers of the constructor and destructors functions in the
       environment signature. These functions should be called only
       after createSymbols() has been called once */
    unsigned functor() {return _functor; }
    unsigned destructorFunctor(unsigned ith) { return _destructors[ith]; }

    bool hasDiscriminator() { return _hasDiscriminator; }
    unsigned discriminator() { ASS(_hasDiscriminator); return _discriminator; }
    void addDiscriminator(unsigned d) { ASS(!_hasDiscriminator); _hasDiscriminator = true; _discriminator = d; }

    Lib::vstring discriminatorName();

    Lib::vstring getCtxFunctionName(TermAlgebra* ta);
    unsigned getCtxFunction(TermAlgebra* ta);
    
  private:
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
    TermAlgebra(unsigned sort,
                Lib::vstring name,
                unsigned n,
                TermAlgebraConstructor** constrs,
                bool allowsCyclicTerms = false);
    ~TermAlgebra() {}

    unsigned sort() { return _sort; }
    unsigned nConstructors() { return _n; }
    TermAlgebraConstructor* constructor(unsigned ith) { ASS_L(ith, _n); return _constrs[ith]; }
    bool allowsCyclicTerms() { return _allowsCyclicTerms; }
    Lib::vstring name() { return _name; }

    /* True iff the algebra defines an empty domain, which could be
       due to:
       - having no constructors
       - not allowing cyclic terms and having only recursive constructors
     */
    bool emptyDomain();
    /* True iff co-datatype with only one unary recursive constructor */
    bool singletonCodatatype();
    /* True iff all the constructors are constants, or singleton co-datatype (false does NOT mean that the domain is necessarily infinite) */
    bool finiteDomain();
    /* True iff  has recursive constructors and not a singleton co-datatype (false does not NOT mean that the domain is necessarily finite) */
    bool infiniteDomain();

    /* True iff a term of the term algebra ta can appear under
       constructors of this algebra */
    bool isMutualType(TermAlgebra* ta);
    Lib::Set<TermAlgebra*>& mutualTypes();

    /* The predicate of the subterm relation for axioms of
       datatypes */
    Lib::vstring getSubtermPredicateName(TermAlgebra* ta);
    unsigned getSubtermPredicate(TermAlgebra* ta);

    /* The constant-context, cycle and application functions, used
       only for axioms of co-datatypes */
    unsigned contextSort(TermAlgebra* ta);
    Lib::vstring getCstFunctionName();
    unsigned getCstFunction();
    Lib::vstring getHoleConstantName();
    unsigned getHoleConstant();
    Lib::vstring getCycleFunctionName();
    unsigned getCycleFunction();
    Lib::vstring getAppFunctionName(TermAlgebra* ta);
    unsigned getAppFunction(TermAlgebra* ta);

  private:
    void setMutualTypes();
    
    unsigned _sort;
    Lib::vstring _name;
    Lib::Set<TermAlgebra*>* _mutualTypes; /* This contains the types mutually defined. null if not initialized, else its content should also be set */
    Lib::Map<TermAlgebra*, unsigned> _contextSorts; /* sorts of context (used to axiomatize codatatypes) */
    unsigned _n; /* number of constructors */
    bool _allowsCyclicTerms;
    ConstructorArray _constrs;
  };
}

#endif

