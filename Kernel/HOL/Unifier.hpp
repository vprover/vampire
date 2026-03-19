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
#include "Lib/Stack.hpp"

using namespace Kernel;
using namespace Shell;

namespace HOL {

class Unifier {
public:
  Unifier(Literal* lit, Literal* def, unsigned nextVar);

  // does one iteration, returns true if finished
  bool iterate(LiteralStack& solution);

private:
  struct Constraint;

  struct Node
  {
    Node(Literal* lit, Literal* def, unsigned nextVar);
    Node(const Node& parent, HOL::UnificationInference inf, unsigned var, TermList binding);
    Node(const Node& parent, HOL::UnificationInference inf, Stack<Constraint> cons);

    std::pair<Stack<Node*>,LiteralStack> solve();

    const Node* _parent = nullptr;
    HOL::UnificationInference _inf;
    Literal* _def;
    Literal* _orig;
    Stack<Constraint> _cons;
    Substitution _subs;
    unsigned _freshVar;
  private:
    Stack<Node*> decompose(unsigned index) const;

    LiteralStack solution() const;
    bool checkSolution(const LiteralStack& ffPairs) const;
  };

  friend std::ostream& operator<<(std::ostream& out, const Constraint& con);
  friend std::ostream& operator<<(std::ostream& out, const Node& node);
  friend std::ostream& operator<<(std::ostream& out, const Unifier& unif);

  Literal* _lit;
  Stack<Node*> _todo;
};

}

#endif // __HOL_Unifier__
