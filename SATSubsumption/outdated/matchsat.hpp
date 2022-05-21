#ifndef MATCHSAT_HPP
#define MATCHSAT_HPP

#include <cstdint>



// CSP solver
//
// - native support for variables with non-binary domain size
// - (boolean variables)
// - exclusive (multiset) matching, i.e., AllDifferent constraint over the non-binary variables
// - clause learning



// /// Boolean variable representing assignment index -> value.
// class Var {
//   std::uint16_t index : 15;  ///< Index of corresponding non-boolean variable
//   std::uint16_t value : 15;  ///< Value of corresponding non-boolean variable
// };



// To clarify:
// - How do we map non-boolean variable assignments to contiguous boolean indices? (=> the 'choices' array could carry an index, and we just carry that along wherever it is needed)
// - What do we actually gain from doing this?
//   => specialized propagation removes need for creating clauses and at-most-one constraints



// See also CPAIOR 2020 Master Class on Constraint Programming (Laurent Perron, Frederic Didier)
//
//
// Encode non-boolean values with boolean variables in two ways:
// For x with domain [l..u]:
// Order encoding:
// - boolean variable [x <= d] for d in l..u-1
// Value encoding:
// - boolean variable [x == d] for d in l..u
// (and clauses to link them together)
//
//
// Propagators need to explain propagations (this gives the reason for CDCL)
//
//
// Encoding is dynamic (not fully created upfront):
// Order encoding:
// - integer literals "x <= d" created on demand (cheap)
// - boolean literals attached to those are only created when branching
// Value encoding:
// - triggered by constraints; if you need value encoding you're usually better off using boolean variables directly instead of integers
// (that last comment seems to suggest we should not go in this direction and rather stay on the SAT level?)



// Peter Stuckey, slides PPDP 2013 "Search is Dead" on lazy clause generation.
// "LCG is SMT", "Each CP propagator is a theory propagator", page 28
// (but also note following slide "LCG is not SMT")
//
// Symmetries and LCG, p. 54ff; also Language of Lemmas, p. 61ff
// Can we use something similar for our pigeonhole-like instances?



#endif /* !MATCHSAT_HPP */
