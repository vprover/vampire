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
 * @file TermTransformer.hpp
 * Defines class TermTransformer.
 */

#ifndef __TermTransformer__
#define __TermTransformer__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"


namespace Kernel {

/**
 * Common methods of TermTransformer and BottomUpTermTransformer extracted here.
 */
class TermTransformerCommon {
public:
  Literal* transformLiteral(Literal* lit);
  virtual Formula* transform(Formula* f) = 0;
  virtual Term* transform(Term* term) = 0;
protected:
  Term* transformSpecial(Term* specialTerm);
  virtual TermList transform(TermList ts) = 0;
};

/**
 * Class to allow for easy transformations of subterms in shared literals.
 *
 * The inheriting class implements function transformSubterm(TermList)
 * and then the functions transform(Literal*)/transform(Term*) use it to transform subterms
 * of the given literal/term.
 *
 * The literal and subterms returned by the transformSubterm(TermList) function have
 * to be shared.
 *
 * This class can be used to transform sort arguments as well by suitably
 * implementing the transformSubterm(TermList) function
 *
 * TermTransformer goes top down but does no recurse into the replaced term
 *
 * Note that if called via transform(Term* term) the given term itself will not get transformed, only possibly its proper subterms
 */
class TermTransformer : public TermTransformerCommon {
public:
  const bool transformSorts;
  virtual ~TermTransformer() {}
  explicit TermTransformer(const bool transformSorts = true) : transformSorts(transformSorts) {}
  Term* transform(Term* term) override;
protected:
  virtual TermList transformSubterm(TermList trm) = 0;
  Formula* transform(Formula* f) override;
  TermList transform(TermList ts) override;

  // default implementation, can override if required
  virtual bool exploreSubterms(TermList orig, TermList newTerm) {
    ASS(newTerm.isTerm());

    return orig == newTerm;
  }
};

template<typename TransformFn, typename ExploreFn>
TermList holTermTransform(TermList tl, TransformFn tfn, ExploreFn efn)
{
  unsigned lambdaLevel = 0;
  // first let's try transforming ts directly
  TermList transformed = tfn(tl, lambdaLevel);
  if (transformed != tl) {
    // we did transform, so we are done if we do not have to explore subterms
    if (transformed.isVar() || !efn(tl, transformed, lambdaLevel)) {
      return transformed;
    }
    tl = transformed;
  } else if (tl.isVar()) {
    // we didn't transform, but it's a var (no way to recurse)
    return tl;
  }
  auto term = tl.term();

  Stack<std::tuple<Term*,TermList*,bool>> todo(8);
  Stack<TermList> args(8);

  auto pushTodo = [&todo,&args,&lambdaLevel](Term* t) {
    if (t->isLambdaTerm()) {
      lambdaLevel++;
    }
    ASS(!t->isSort() && !t->isLiteral() && !t->isSpecial());
    auto targs = t->args();
    while (targs != t->termArgs()) {
      args.push(*targs);
      targs = targs->next();
    }
    todo.emplace(t, targs, false);
  };
  pushTodo(term);

  while (todo.isNonEmpty()) {
    auto& [orig, tt, modified] = todo.top();

    if (tt->isEmpty()) {
      if (orig->isLambdaTerm()) {
        lambdaLevel--;
      }
      todo.pop();
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      auto argLst = args.end() - orig->arity();
      // potentially evil. Calls destructors on the truncated
      // objects, which we are happily reading just below
      args.truncate(args.length() - orig->arity());
      if (modified) {
        args.emplace(Term::create(orig,argLst));
        if (todo.isNonEmpty()) {
          get<2>(todo.top()) = true;
        }
      } else {
        args.emplace(orig);
      }
      continue;
    }
    TermList tl = *tt;
    tt = tt->next();

    TermList dest = tfn(tl, lambdaLevel);
    if (tl != dest) {
      modified = true;
    }
    if (dest.isVar() || !efn(tl, dest, lambdaLevel)) {
      args.push(dest);
      continue;
    }
    pushTodo(dest.term());
  }

  ASS_EQ(args.size(), 1);
  return args.pop();
}

/**
 * Has similar philosophy to TermTransformer, but:
 *  goes bottom up and so subterms of currently considered terms
 *  might already be some replacements that happened earlier, e.g.:
 *  transforming g(f(a,b)) will consider (provided transformSubterm is the identity function)
 *  the following sequence: a,b,f(a,b),g(f(a,b))
 *  and if transformSubterm is the identity everywhere except for f(a,b) for which it returns c,
 *  the considered sequence will be: a,b,f(a,b)->c,g(c)
 */
class BottomUpTermTransformer : public TermTransformerCommon {
public:
  virtual ~BottomUpTermTransformer() {}
  explicit BottomUpTermTransformer(const bool transformSorts = true) : transformSorts(transformSorts) {}
  Term* transform(Term* term) override;
protected:
  virtual TermList transformSubterm(TermList trm) = 0;
  /**
   * Lets a subclass declare that a term needs no transformation at all - neither it
   * nor anything below it. Such a term is used as it is: it is not descended into and
   * transformSubterm is not called on it. Only sound if the subclass can tell that
   * transforming the whole subtree would be the identity.
   */
  virtual bool alreadyTransformed(Term* t) { return false; }
  Formula* transform(Formula* f) override;
  TermList transform(TermList ts) override;

  const bool transformSorts;
};


}

#endif // __TermTransformer__
