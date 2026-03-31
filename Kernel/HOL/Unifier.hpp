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
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Stack.hpp"

using namespace Kernel;
using namespace Shell;

namespace HOL {

class Unifier {
public:
  Unifier(Literal* lit, Literal* def, unsigned nextVar);

  // does one iteration, returns true if finished
  bool iterate(LiteralStack& solution);
  bool simplify(LiteralStack& solution);

  static TermList applyTermSpec(TermSpec t, RobSubstitution& subs, DHMap<VarSpec, unsigned>& varMap);

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

  struct Node
  {
    Node(Literal* lit, Literal* def, unsigned nextVar);
    Node(const Node& parent, HOL::UnificationInference inf, unsigned var, TermList binding);
    Node(const Node& parent, HOL::UnificationInference inf, Stack<Constraint> cons);

    std::pair<Stack<Node*>,LiteralStack> solve();
    bool simplify();
    Recycled<Stack<UnificationConstraint>> toUnif() const;

    const Node* _parent = nullptr;
    HOL::UnificationInference _inf;
    Literal* _def;
    Literal* _orig;
    Stack<Constraint> _cons;
    Substitution _subs;
    unsigned _freshVar;
  private:
    Stack<Constraint> decompose(unsigned index) const;

    LiteralStack solution() const;
    bool checkSolution(const LiteralStack& ffPairs) const;
  };

  friend std::ostream& operator<<(std::ostream& out, const Constraint& con);
  friend std::ostream& operator<<(std::ostream& out, const Node& node);
  friend std::ostream& operator<<(std::ostream& out, const Unifier& unif);

private:
  Literal* _lit;
  Stack<Node*> _todo;
};

}

#endif // __HOL_Unifier__
