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
 * @file Unifier.hpp
 * Defines class Unifier for HOL unification.
 */

#ifndef __HOL_Unifier__
#define __HOL_Unifier__

#include "Forwards.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Stack.hpp"

using namespace Kernel;
using namespace Shell;

namespace HOL {

/**
 * This class represents a HO unification "state", with some to-be-handled unification constraints,
 * and a partial unifier. The unifier is extended such that it stays idempotent, the caller has to
 * ensure this by calling the constructor with a `nextVar` argument that represents a fresh variable
 * among the constraints, and the substitution. Mostly following the transitions from "Efficient
 * Full Higher-order Unification" from Vukmirovic et al.
 */
struct UnificationNode
{
  struct Constraint
  {
    TermList _lhs;
    TermList _rhs;
    TermList _sort;
    TermList _lhead;
    TermList _rhead;

    Constraint(TermList lhs, TermList rhs, TermList sort);

    inline bool flexFlex() const { return _lhead.isVar() && _rhead.isVar(); }
    inline bool rigidRigid() const { return _lhead.isTerm() && _rhead.isTerm(); }
    inline bool flexRigid() const { return !flexFlex() && !rigidRigid(); }

    bool derefHead(TermList& head, TermList& side, const Substitution& subs);
    void normalize(const Substitution& subs);
  };

  UnificationNode(Stack<Constraint> cons, unsigned nextVar);

  /** This function should be called when extending the current unifier is allowed,
   * i.e. when we haven't reached the maximum allowed unification depth yet. */
  Option<Stack<UnificationNode*>> solve();
  /** This function should be called when we want to simplify the constraints
   * as much as possible, possibly before returning an abstraction. */
  bool simplify();

  Stack<Constraint> _cons;
  Substitution _subs;
private:
  UnificationNode(const UnificationNode& parent, unsigned var, TermList binding);
  UnificationNode(const UnificationNode& parent, Stack<Constraint> cons);
  Stack<Constraint> decompose(unsigned index, bool includeRest) const;

  unsigned _freshVar;
};

/**
 * Wrapper around an abstracting unifier that may contain HO unification constraints.
 * It takes an abstracting unifier and tries to solves its constraints, or instantiates
 * variables until a certain limit (this is set by the depth parameter, which is the
 * number of variables instantiated on a given branch in the HOL unification tree).
 */
class AbstractingWrapper
  : public IteratorCore<AbstractingUnifier*>
{
public:
  AbstractingWrapper(AbstractingUnifier* unifier, unsigned hoUnifDepth);
  ~AbstractingWrapper();
  AbstractingWrapper(const AbstractingWrapper&) = delete;
  AbstractingWrapper& operator=(const AbstractingWrapper&) = delete;

  DECL_ELEMENT_TYPE(AbstractingUnifier*);

  bool hasNext();
  AbstractingUnifier* next();

private:
  AbstractingUnifier* _unifier;
  const unsigned _hoUnifDepth;
  BacktrackData _localBD;
  Stack<std::pair<UnificationNode*, unsigned>> _todo;
  UnificationNode* _next = nullptr;
};

}

#endif // __HOL_Unifier__
