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
 * @file ClauseVariantIndex.hpp
 * Defines class ClauseVariantIndex.
 */


#ifndef __ClauseVariantIndex__
#define __ClauseVariantIndex__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

#include "Kernel/Term.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

class ClauseVariantIndex
{
public:
  virtual ~ClauseVariantIndex() {};

  virtual void insert(Clause* cl) = 0;

  virtual ClauseIterator retrieveVariants(Literal* const * lits, unsigned length) = 0;
  ClauseIterator retrieveVariants(Clause* cl)
  {
    // std::cout << "retrieveVariants for " <<  cl->toString() << std::endl;

    return retrieveVariants(cl->literals(), cl->length());
  }
protected:
  class ResultClauseToVariantClauseFn;
};

class HashingClauseVariantIndex : public ClauseVariantIndex
{
public:
  ~HashingClauseVariantIndex() override;

  void insert(Clause* cl) override;

  ClauseIterator retrieveVariants(Literal* const * lits, unsigned length) override;

private:
  struct VariableIgnoringComparator;

  /** occurrences of each variable, indexed by its number; hashed as unsigned char (overflows allowed) */
  struct VarCounts {
    Stack<unsigned> counts;
    Stack<unsigned> seen;
    void reset() {
      for (unsigned v : iterTraits(seen.iter())) counts[v] = 0;
      seen.reset();
    }
    void count(unsigned v) {
      while (counts.size() <= v) counts.push(0);
      if (counts[v]++ == 0) seen.push(v);
    }
    unsigned size() const { return seen.size(); }
  };

  unsigned termFunctorHash(const Term* t, unsigned hash_begin) {
    unsigned func = t->functor();
    // std::cout << "will hash funtor " << func << std::endl;
    return FnvHash::hash(func, hash_begin);
  }

  unsigned computeHashAndCountVariables(unsigned var, VarCounts& varCnts, unsigned hash_begin) {
    const unsigned varHash = 1u;

    varCnts.count(var);

    // std::cout << "will hash variable" << std::endl;
    return FnvHash::hash(varHash, hash_begin);
  }

  unsigned computeHashAndCountVariables(TermList* tl, VarCounts& varCnts, unsigned hash_begin);
  unsigned computeHashAndCountVariables(Literal* l, VarCounts& varCnts, unsigned hash_begin);

  unsigned computeHash(Literal* const * lits, unsigned length);

  DHMap<unsigned, ClauseList*, FnvHash, IdentityHash> _entries;
};

};

#endif /* __ClauseVariantIndex__ */
