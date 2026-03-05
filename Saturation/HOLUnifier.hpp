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

namespace Saturation {

class HOLUnifier {
public:
  Clause* handleClause(Clause* cl);
  ClauseStack iterate(unsigned num);

  static bool isHolUnifiable(TermList t);

private:
  Literal* introduceDefinition(Literal* lit);

  struct Constraint;

  struct Node
  {
    Node(Literal* lit, Literal* def, unsigned nextVar);
    Node(const Node* parent, unsigned TODO);

    Literal* solution();
    Node* next();

    Literal* _def;
    Stack<Constraint> _cons;
    Substitution _subs;
    unsigned _freshVar;
  };

  friend std::ostream& operator<<(std::ostream& out, const Constraint& con);
  friend std::ostream& operator<<(std::ostream& out, const Node& node);

  Stack<FormulaUnit*> _defs;
  Stack<Node*> _roots;
  DHMap<Literal*, unsigned> _defPredMap;

  Stack<Node*> _todo;
  unsigned _index = 0;
};

}

#endif // __HOLUnifier__
