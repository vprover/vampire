/*
 * SubstitutionTheory.hpp
 * Copyright (C) 2020 Jakob Rath <git@jakobrath.eu>
 *
 * Distributed under terms of the MIT license.
 */

#ifndef SUBSTITUTIONTHEORY_HPP
#define SUBSTITUTIONTHEORY_HPP

#include "SMTSubsumption/MapBinder.hpp"
#include "Kernel/Term.hpp"
#include "Lib/STL.hpp"
#include "SMTSubsumption/minisat/SolverTypes.h"

#include <algorithm>

namespace SMTSubsumption {

using namespace Kernel;


/// Domain of the substitution: Vampire's FOL variables
using domain = unsigned;

/// Range of the substitution: Vampire's FOL terms
using range = TermList;


class SubstitutionAtom
{
  public:
    explicit
    SubstitutionAtom(vvector<std::pair<domain, range>>&& subst)
      : subst{std::move(subst)}
    { }

    explicit
    SubstitutionAtom(MapBinder const& binder)
    {
      auto const& bindings = binder.bindings();
      subst.reserve(bindings.size());
      for (auto p : bindings) {
        subst.push_back(p);
      }
      std::sort(subst.begin(), subst.end());
    }

    static SubstitutionAtom from_binder(MapBinder const& binder)
    {
      return SubstitutionAtom(binder);
    }

    vvector<std::pair<domain,range>> const& mapping() const
    {
      return subst;
    }

  private:
    /// Bindings sorted by first component
    vvector<std::pair<domain, range>> subst;

    friend std::ostream& operator<<(std::ostream& o, SubstitutionAtom const& atom);
};  // class SubstitutionAtom

std::ostream& operator<<(std::ostream& o, SubstitutionAtom const& atom);



class SubstitutionTheoryConfiguration
{
  public:
    /// Attach theory meaning to a propositional variable.
    /// NOTE: for now, this must be called for all variables in ascending order.
    void register_atom(Minisat::Var var, SubstitutionAtom&& atom)
    {
      ASS_EQ(atoms.size(), var);
      atoms.push_back(std::move(atom));
    }

  private:
    /// Maps boolean variables to the theory atoms they represent.
    /// Dense mapping from Minisat::Var to SubstitutionAtom;
    /// this works because we have no purely boolean variables.
    vvector<SubstitutionAtom> atoms;

    friend class SubstitutionTheory;
};


// For maps where the keys are contiguous non-negative integers
template < typename K, typename V >
using vector_map = vvector<V>;


class SubstitutionTheory
{
  private:
    /// Maps boolean variables to the theory atoms they represent
    vector_map<Minisat::Var, SubstitutionAtom> atoms;

    /// Maps FOL variables to the list of substitution constraints for this variable
    vector_map<domain, vvector<std::pair<range, Minisat::Var>>> atoms_by_domain;

    // // TODO: can we not just use the trail of the solver???
    // vvector<Minisat::Var> trail;
    // vvector<int>          trail_lim;        // Separator indices for different decision levels in 'trail', i.e., trail[trail_lim[dl]] is the first variable at level dl

    // /// Map: domain -> GClause
    // /// The reason why this mapping has become active.
    // vector_map<domain, Minisat::GClause> reason;

    // Current substitution
    // Maps substitution domain (FOL variables) to substitution range (FOL terms)
    // TODO: we probably don't even need that. why? because of exhaustive theory propagation, we never get conflicts. maybe keep this for assertions in debug mode (for now).
    //       (it will be necessary for subsumption demodulation, to build the rewritten term)
    // TODO: potential problem because FOL variables are not contiguous.
    // TODO: possible (partial) solution: ImmediateSimplificationRule that normalizes variable indices (e.g., if max index > 100?)
    // Idea for easier backjumping: add trail index when it was set (or maybe decision level is enough),
    //                              and only consider the value to be set if the current trail index is larger than the stored one.
    vector_map<domain, range> current_substitution;

  public:
    /// Decision level in the SAT solver, for backtracking
    using Level = int;

    // empty substitution theory
    SubstitutionTheory()
    { }

    SubstitutionTheory& operator=(SubstitutionTheory&& other) = default;

    explicit
    SubstitutionTheory(SubstitutionTheoryConfiguration&& config)
      : atoms{std::move(config.atoms)}
    {
      domain max_d = 0;
      for (auto const& atom : atoms) {
        for (auto const& p : atom.mapping()) {
          max_d = std::max(max_d, p.first);
          ASS(p.second.isNonEmpty());  // we use empty TermLists to mean "unassigned"
        }
      }
      std::cerr << "max_d = " << max_d << std::endl;

      TermList t_empty;
      t_empty.makeEmpty();
      current_substitution.resize(max_d+1, t_empty);
      ASS(std::all_of(current_substitution.begin(), current_substitution.end(), [](range t) { return t.isEmpty(); }));

      atoms_by_domain.resize(max_d+1);
      for (Minisat::Var var = 0; var < atoms.size(); ++var) {
        auto const& atom = atoms[var];
        for (auto const& p : atom.mapping()) {
          std::cerr << var << ": " << p.first << " -> " << p.second << std::endl;
          atoms_by_domain[p.first].push_back({ p.second, var });
        }
      }

      // Minisat::GClause gc_empty = Minisat::GClause_new(nullptr);
      // reason.resize(max_d+1, gc_empty);
      // // reason.reserve(max_d);
      // // for (size_t i = 0; i < max_d; ++i) {
      // //   reason.push_back(GClause_NULL);
      // // }
      // ASS(std::all_of(reason.begin(), reason.end(), [](Minisat::GClause gc) { return gc.isNull(); }));
    }

    /// Call this when a SAT variable has been set to true
    /// PropagateCallback ~ bool(Minisat::Lit propagated,GClause)
    template < typename PropagateCallback >
    bool enable(Minisat::Var var, /* Level level, Minisat::GClause reason, */ PropagateCallback propagate)
    {
      std::cerr << "SubstitutionTheory::enable: " << var << std::endl;
      // Since all our propositional variables have some theory meaning attached,
      // we can assert this.
      // Otherwise we should need whether the variable has some theory component
      // and only proceed if it does.
      ASS_L(var, atoms.size());
      SubstitutionAtom const& atom = atoms[var];

// #if DEBUG
//       // var should be unassigned (this is to be ensured by the calling SAT solver)
//       ASS(std::all_of(trail.begin(), trail.end(), [var](Minisat::Var w) { w != var }));
// #endif

#if DEBUG
      // Must be compatible due to exhaustive theory propagation
      for (auto p : atom.mapping()) {
        range current = current_substitution[p.first];
        ASS(current.isEmpty() || current == p.second);
      }
#endif

      // // Update state
      // trail.push_back(var);   // TODO record level
      // for (auto p : atom.mapping()) {
      //   current_substitution[p.first] = p.second;
      // }

      // TODO: instead of explicitly propagating, add binary clause (to store it inside watch lists)
      //       (still have to examine same FOL variable later again)
      // Actually: this may not be what we want after all.
      // What we do now is theory propagation, this would be theory learning.
      // According to the SMT paper this is generally not as useful (since we then duplicate theory propagation work into the SAT part).

      // Exhaustively propagate conflicting atoms
      for (auto p : atom.mapping()) {  // go through list of constraints (x -> t)

        // TODO: if p.first already assigned, skip

        // p: (domain, range)  -- one particular mapping of the newly-enabled substitution
        //    (Vampire::Variable, TermList)
        for (auto q : atoms_by_domain[p.first]) {  // other constraints with x  ( x-> t1, ...)
          // atoms_by_domain[p.first]: list of all other possible mappings for the affected domain value
          // q: (range, Minisat::Var)  -- range value of the corresponding substitution atom and the minisat variables that would lead to this choice
          if (q.first != p.second) {

            // conflicting substitutions, propagate conflicting_var to false.
            Minisat::Var conflicting_var = q.second;
            Minisat::Lit propagated_lit = ~Minisat::Lit(conflicting_var);

            // // The reason as clause is:  ¬var \/ propagated_lit
            // Minisat::vec<Minisat::Lit> reason_lits;
            // // TODO: Order [propagated_lit, ~var] works, but assertion failure with [~var, propagated_lit] ??????  => check minisat code again, maybe the order is significant? (e.g., like first literal in learned clauses)
            // reason_lits.push(propagated_lit);
            // reason_lits.push(~Minisat::Lit(var));
            // Minisat::Clause* reason_cl = Minisat::Clause_new(false, reason_lits);  // TODO: memory leak?
            // Minisat::GClause reason = Minisat::GClause_new(reason_cl);

            // Minisat has special handling for binary clauses as reasons.
            // They can be stored as a single literal, because unary clauses never appear as reason.
            // This saves an allocation.
            // TODO: look more closely at minisat code to confirm this.
            Minisat::GClause reason = Minisat::GClause_new(~Minisat::Lit(var));

            if (!propagate(propagated_lit, reason)) {
              // Conflict in solver, no use in further propagation
              return false;
            }
          }
        }
      }

      return true;
    }

    /// Undo all assignments above the given level
    void backjump(Level level)
    {
      // TODO reset current_substitution
    }
};


}

#endif /* !SUBSTITUTIONTHEORY_HPP */
