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
 * @file HOL.hpp
 */

#ifndef HOL_HPP
#define HOL_HPP

#include "Kernel/Signature.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/Environment.hpp"

/**
 * This namespace contains several helper functions to deal with higher-order terms.
 * It will eventually replace the legacy ApplicativeHelper
 */
namespace HOL {

#if VDEBUG
  #define LOG(...)   ::HOL::print_debug(__REL_FILE__, __LINE__, __VA_ARGS__)
  #define LOGE(expr) ::HOL::print_debug(__REL_FILE__, __LINE__, #expr, expr)
#else
  #define LOG(...)
  #define LOGE(expr)
#endif

template<class... A>
void print_debug(const char* file, unsigned line, const A&... msg) {
  for (unsigned i = 0; i < Debug::debugConfig.indent; ++i)
    std::cout << "  ";

  std::cout << "|LOG " << file << ":" << line << " @ ";
  ((std::cout << " " << msg), ...);
  std::cout << std::endl;
}

using Kernel::Term;
  
inline bool isTrue(TermList term) {
  return term.isTerm() && env.signature->isFoolConstantSymbol(true, term.term()->functor());
}

inline bool isFalse(TermList term) {
  return term.isTerm() && env.signature->isFoolConstantSymbol(false, term.term()->functor());
}

std::string toString(const Term &term, bool topLevel);

TermList matrix(TermList t);
void getHeadAndArgs(TermList term, TermList &head, Kernel::TermStack &args);

TermList getNthArg(TermList arrowSort, unsigned argNum);
TermList getResultAppliedToNArgs(TermList arrowSort, unsigned argNum);
unsigned getArity(TermList sort);
TermList getDeBruijnIndex(int index, TermList sort);

inline bool canHeadReduce(const TermList& head, const TermStack& args) { return head.isLambdaTerm() && args.size(); }
} // namespace HOL

namespace HOL::create {
  TermList app(TermList sort, TermList head, TermList arg);
  TermList app(TermList head, TermList arg);
  TermList app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared = true);
  TermList app(TermList sort, TermList head, TermStack& terms); // todo const termstack

  inline TermList app2(TermList sort, TermList head, TermList arg1, TermList arg2) {
    return app(app(sort, head, arg1), arg2);
  }

  inline TermList app2(TermList head, TermList arg1, TermList arg2) {
    ASS(head.isTerm())

    return app2(Kernel::SortHelper::getResultSort(head.term()), head, arg1, arg2);
  }

  inline TermList equality(TermList sort) { return TermList(Term::create1(env.signature->getEqualityProxy(), sort)); }
  inline TermList neg() { return TermList(Term::createConstant(env.signature->getNotProxy())); }
  inline TermList pi(TermList sort) { return TermList(Term::create1(env.signature->getPiSigmaProxy("vPI"), sort)); }
  inline TermList sigma(TermList sort) { return TermList(Term::create1(env.signature->getPiSigmaProxy("vSIGMA"), sort)); }

  Term *lambda(std::initializer_list<unsigned> vars, std::initializer_list<TermList> varSorts, Kernel::TypedTermList body);
  TermList lambda(TypedTermList var, TypedTermList body);

  TermList namelessLambda(TermList varSort, TermList termSort, TermList term);
  TermList namelessLambda(TermList varSort, TermList term);
} // namespace HOL::create

namespace HOL::convert {

TermList toNameless(TermList term);

inline TermList toNameless(Term* term) {
  return toNameless(TermList(term));
}

} // namespace HOL::convert

namespace HOL::reduce {
TermList betaNF(TermList t);
TermList betaNF(TermList t, unsigned *reductions);
} // namespace HOL::reduce

#endif // HOL_HPP
