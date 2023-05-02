/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef LITERALBYMATCHABILITY_HPP
#define LITERALBYMATCHABILITY_HPP

#include "Clause.hpp"
#include "Term.hpp"
#include <utility>

namespace Kernel {


/**
 * A literal and its rating (for use in the subsumption index).
 * Ordered by ratings, breaking ties with the literal's id.
 *
 * The metric used to select the best literal is defined as follows:
 *
 *    val == num(symbols) - num(distinct-variables)
 *        == num(non-variable-symbols) + num(variable-duplicates)
 *
 * This value is the number of symbols that induce constraints for matching.
 * Note that variables only induce constraints for instantiation on their
 * repeated occurrences.  We want to maximize this value to have the most
 * restricting literal, so we get as little candidate clauses as possible
 * (because the candidates then have to be passed to the MLMatcher which is
 * expensive).
 */
class LiteralByMatchability
{
  private:
    Literal* m_lit;
    unsigned m_val;

  public:
    LiteralByMatchability(Literal* lit)
      : m_lit(lit), m_val(computeRating(lit))
    { }

    static unsigned computeRating(Literal* lit)
    {
      return lit->weight() - lit->getDistinctVars();
    }

    Literal* lit() const { return m_lit; }

    bool operator<(LiteralByMatchability const& other) const
    {
      return m_val < other.m_val || (m_val == other.m_val && m_lit->getId() < other.m_lit->getId());
    }
    bool operator>(LiteralByMatchability const& other) const { return other.operator<(*this); }
    bool operator<=(LiteralByMatchability const& other) const { return !operator>(other); }
    bool operator>=(LiteralByMatchability const& other) const { return !operator<(other); }
    bool operator==(LiteralByMatchability const& other) const { return m_lit == other.m_lit; }
    bool operator!=(LiteralByMatchability const& other) const { return !operator==(other); }

    static LiteralByMatchability find_least_matchable_in(Clause* c)
    {
      ASS_GE(c->length(), 1);
      LiteralByMatchability best{(*c)[0]};
      for (unsigned i = 1; i < c->length(); ++i) {
        LiteralByMatchability curr{(*c)[i]};
        if (curr > best) {
          best = curr;
        }
      }
      return best;
    }

    static std::pair<LiteralByMatchability,LiteralByMatchability> find_two_least_matchable_in(Clause* c)
    {
      ASS_GE(c->length(), 2);
      LiteralByMatchability best{(*c)[0]};
      LiteralByMatchability secondBest{(*c)[1]};
      if (secondBest > best) {
        std::swap(best, secondBest);
      }
      for (unsigned i = 2; i < c->length(); ++i) {
        LiteralByMatchability curr{(*c)[i]};
        if (curr > best) {
          secondBest = best;
          best = curr;
        } else if (curr > secondBest) {
          secondBest = curr;
        }
      }
      ASS(best.lit() != secondBest.lit());
      ASS(best > secondBest);
      return {best, secondBest};
    }
};


}

#endif /* !LITERALBYMATCHABILITY_HPP */
