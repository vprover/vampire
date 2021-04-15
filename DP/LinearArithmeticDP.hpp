
/*
 * File LinearArithmeticDP.hpp.
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
/**
 * @file LinearArithmeticDP.hpp
 * Defines class LinearArithmeticDP for implementing congruence closure
 */

#ifndef __LinearArithmeticDP__
#define __LinearArithmeticDP__

#define DLADP 0

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Deque.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/List.hpp"
#include "Shell/Options.hpp"
#include <vector>
#include <set>
#include <map>

#include "Kernel/Term.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Theory.hpp"

#include "DecisionProcedure.hpp"
#include "LinearArithmeticSolverDP.hpp"

namespace DP {

using namespace Lib;
using namespace Kernel;

/**
 * General class for DPs for linear arithmetic
 * This class extracts a LA problem from the literals and then passes it elsewhere
 * to be solved. 
 */
class LinearArithmeticDP : public DecisionProcedure {
public:
  CLASS_NAME(LinearArithmeticDP);
  USE_ALLOCATOR(LinearArithmeticDP);
  BYPASSING_ALLOCATOR;

  LinearArithmeticDP();
  ~LinearArithmeticDP();

  virtual void addLiterals(LiteralIterator lits, bool onlyEqualites) override;

  virtual Status getStatus(bool retrieveMultipleCores) override;

  virtual unsigned getUnsatCoreCount() override;
  virtual void getUnsatCore(LiteralStack &res, unsigned coreIndex) override;

  virtual void getModel(LiteralStack &model) override;

  virtual void reset() override;

  // Constraint represents
  // Sum of parameters <predicate> constant
  // where predicate will always be < or <= later
  // see toString
  struct Constraint {
    // domain is functor symbols
    map<unsigned, RationalConstantType> parameters;
    RationalConstantType constant = RationalConstantType(0);
    Interpretation predicate;
    Literal *parent;

    string toString()
    {
      string str = "";
      for (auto const &parameter : parameters) {
        str += "ParameterID: " + to_string(parameter.first) + ", coefficient: " + parameter.second.toString().c_str() + "\n";
      }

      switch (predicate) {
        case Interpretation::EQUAL:
          str += "Predicate: =\n";
          break;
        case Interpretation::INT_GREATER:
        case Interpretation::RAT_GREATER:
        case Interpretation::REAL_GREATER:
          str += "Predicate: >\n";
          break;
        case Interpretation::INT_GREATER_EQUAL:
        case Interpretation::RAT_GREATER_EQUAL:
        case Interpretation::REAL_GREATER_EQUAL:
          str += "Predicate: >=\n";
          break;
        case Interpretation::INT_LESS:
        case Interpretation::RAT_LESS:
        case Interpretation::REAL_LESS:
          str += "Predicate: <\n";
          break;
        case Interpretation::INT_LESS_EQUAL:
        case Interpretation::RAT_LESS_EQUAL:
        case Interpretation::REAL_LESS_EQUAL:
          str += "Predicate: <=\n";
          break;
        default:
          break;
      }

      str += "Constant: " + string(constant.toString().c_str());

      return str;
    }
  };

  struct Cache {
    // Set solver DP when intializing solvers
    Shell::Options::LinearArithmeticDP solverType;
    LinearArithmeticSolverDP *solverDP;
    vector<Literal *> constraints;

    map<Literal *, Constraint> parsedLiterals;
  };

  bool addSolverDPIfInCache();
  bool addConstraintIfInCache(Literal *lit);

private:
  LinearArithmeticSolverDP *solverDP;
  vector<Constraint> parsedLiterals;

  Cache cache;

  void addLiteral(Literal *lit);
  void toParams(Term *term, RationalConstantType coef, Constraint *parData);
};

} // namespace DP

#endif // __LinearArithmeticDP__
