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
 * @file HOLUnifier.hpp
 * Defines class HOLUnifier for dovetailing of HOL unifiers.
 */

#ifndef __HOLUnifier__
#define __HOLUnifier__

#include "Forwards.hpp"
#include "Kernel/Substitution.hpp"
#include "Lib/Stack.hpp"
#include "Lib/DHMap.hpp"

using namespace Kernel;
using namespace Shell;

namespace Saturation {

class HOLUnifier {
public:
  HOLUnifier(const Options& opt);

  Clause* handleClause(Clause* cl);
  ClauseStack iterate();

  static bool isHolUnifiable(TermList t);

private:
  std::pair<Literal*,Unit*> introduceDefinition(Literal* lit);

  struct Constraint;

  struct Node
  {
    Node(Literal* lit, Literal* def, unsigned nextVar);
    Node(const Node& parent, unsigned var, TermList binding);
    Node(const Node& parent, Stack<Constraint> cons);

    std::pair<Stack<Node*>,LiteralStack> solve();

    Literal* _def;
    Stack<Constraint> _cons;
    Substitution _subs;
    unsigned _freshVar;
  private:
    LiteralStack solution();
  };

  friend std::ostream& operator<<(std::ostream& out, const Constraint& con);
  friend std::ostream& operator<<(std::ostream& out, const Node& node);

  struct UCDef {
    unsigned pred;
    FormulaUnit* def;
  };
  DHMap<Literal*, UCDef> _litToDefMap;

  Stack<Node*> _roots;
  Stack<Node*> _todo;

  const unsigned _kNumIter;
};

}

#endif // __HOLUnifier__
