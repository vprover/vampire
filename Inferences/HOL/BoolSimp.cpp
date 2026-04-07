/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SortHelper.hpp"

#include "Kernel/HOL/SubtermReplacer.hpp"

#include "BoolSimp.hpp"

namespace Inferences {

Clause* BoolSimp::simplify(Clause* premise)
{
  for (const auto& lit : *premise) {
    // Below should be safe. We can bool simplify a term that contains free indices
    for (const auto& st : iterTraits(NonVariableNonTypeIterator(lit))) {
      if (!SortHelper::getResultSort(st).isBoolSort()) {
        continue;
      }
      auto simpSt = boolSimplify(st);
      if (simpSt == TermList(st)) {
        continue;
      }
      RStack<Literal*> resLits;
      SubtermReplacer replacer(TermList(st), simpSt, /*liftFree=*/false);
      for (const auto& curr : *premise) {
        resLits->push(lit == curr ? replacer.transformLiteral(curr) : curr);
      }
      return Clause::fromStack(*resLits, SimplifyingInference1(InferenceRule::BOOL_SIMP, premise));
    }
  }
  return premise;
}

bool BoolSimp::complementary(TermStack args)
{
  ASS_EQ(args.size(), 2);
  static TermStack aArgs;

  auto head = HOL::getHeadAndArgs(args[0], aArgs);
  if (head.isProxy(Proxy::NOT) && aArgs[0] == args[1]) {
    return true;
  }

  head = HOL::getHeadAndArgs(args[1], aArgs);
  if (head.isProxy(Proxy::NOT) && aArgs[0] == args[0]) {
    return true;
  }

  return false;
}

TermList BoolSimp::boolSimplify(Term* term)
{
  auto negate = [](TermList t) {
    return HOL::create::app(HOL::create::neg(), t);
  };

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());
  static TermStack args;

  // NOTE: arguments are stored *backwards* in args
  auto head = HOL::getHeadAndArgs(TermList(term), args);

  if (head.isVar()) {
    return TermList(term);
  }

  switch (env.signature->getFunction(head.term()->functor())->proxy()) {
    case Proxy::AND: {
      ASS_EQ(args.size(), 2);
      if (args[0] == fols || args[1] == fols || complementary(args)) { return fols; }
      if (args[0] == troo)                                           { return args[1]; }
      if (args[1] == troo || args[0] == args[1])                     { return args[0]; }
      break;
    }
    case Proxy::OR: {
      ASS_EQ(args.size(), 2);
      if (args[0] == troo || args[1] == troo || complementary(args)) { return troo; }
      if (args[0] == fols)                                           { return args[1]; }
      if (args[1] == fols || args[0] == args[1])                     { return args[0]; }
      break;
    }
    case Proxy::IMP: {
      ASS_EQ(args.size(), 2);
      if (args[1] == fols || args[0] == troo || args[0] == args[1]) { return troo; }
      if (args[1] == troo || complementary(args))                   { return args[0]; }
      if (args[0] == fols)                                          { return negate(args[1]); }
      break;
    }
    case Proxy::IFF: {
      ASS_EQ(args.size(), 2);
      if (args[0] == troo)     { return args[1]; }
      if (args[1] == troo)     { return args[0]; }
      if (args[0] == fols)     { return negate(args[1]); }
      if (args[1] == fols)     { return negate(args[0]); }
      if (args[0] == args[1])  { return troo; }
      if (complementary(args)) { return fols; }
      break;
    }
    case Proxy::NOT: {
      ASS_EQ(args.size(), 1);
      if (args[0] == troo) { return fols; }
      if (args[0] == fols) { return troo; }
      auto head = HOL::getHeadAndArgs(args[0], args);
      if (head.isProxy(Proxy::NOT)) {
        ASS_EQ(args.size(), 1);
        return args[0];
      }
      break;
    }
    case Proxy::EQUALS: {
      ASS_EQ(args.size(), 2);
      if (args[0] == args[1]) { return troo; }
      break;
    }
    default:
      break;
  }
  return TermList(term);
}

}
