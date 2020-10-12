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
    // vvector<SubstitutionAtom> atoms;

    vector_map<domain, vvector<std::pair<range, Minisat::Var>>> atoms_by_domain;

    // TODO: can we not just use the trail of the solver???
    vvector<Minisat::Var> trail;
    vvector<int>          trail_lim;        // Separator indices for different decision levels in 'trail', i.e., trail[trail_lim[dl]] is the first variable at level dl

    /// Map: domain -> GClause
    /// The reason why this mapping has become active.
    vector_map<domain, Minisat::GClause> reason;

    // Current substitution
    // Maps substitution domain (FOL variables) to substitution range (FOL terms)
    // TODO: we probably don't even need that. why? because of exhaustive theory propagation, we never get conflicts. maybe keep this for assertions in debug mode (for now).
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

      Minisat::GClause gc_empty = Minisat::GClause_new(nullptr);
      reason.resize(max_d+1, gc_empty);
      // reason.reserve(max_d);
      // for (size_t i = 0; i < max_d; ++i) {
      //   reason.push_back(GClause_NULL);
      // }
      ASS(std::all_of(reason.begin(), reason.end(), [](Minisat::GClause gc) { return gc.isNull(); }));
    }

    /// Call this when a SAT variable has been set to true
    /// PropagateCallback ~ bool(Minisat::Lit propagated,GClause)
    template < typename PropagateCallback >
    void enable(Minisat::Var var, /* Level level, Minisat::GClause reason, */ PropagateCallback propagate)
    {
      std::cerr << "SubstitutionTheory::enable: " << var << std::endl;
      // Since all our propositional variables have some theory meaning attached,
      // we can assert this.
      // Otherwise we should need whether the variable has some theory component
      // and only proceed if it does.
      ASS_L(var, atoms.size());
      SubstitutionAtom const& atom = atoms[var];

#if DEBUG
      // var should be unassigned (this is to be ensured by the calling SAT solver)
      ASS(std::all_of(trail.begin(), trail.end(), [var](Minisat::Var w) { w != var }));
#endif

#if DEBUG
      // Must be compatible due to exhaustive theory propagation
      for (auto p : atom.mapping()) {
        range current = current_substitution[p.first];
        ASS(current.isEmpty() || current == p.second);
      }
#endif

      // Update state
      trail.push_back(var);   // TODO record level
      for (auto p : atom.mapping()) {
        current_substitution[p.first] = p.second;
      }

      // Exhaustively propagate conflicting atoms
      for (auto p : atom.mapping()) {
        // Needs: a map back from SubstitutionAtom.first to boolean vars
        // We iterate over values for p.first and if they're incompatible, add a binary clause to the SAT solver? maybe not
        // What we discussed: directly set it to true, with the reason coming from the initial assignment (for the SAT-solver it's then indistinguishable from a SAT-propagated variable)
        // But this can be done in the propagate callback; which probably defined in minisat::Solver and just calls enqueue or something like that.
        for (auto q : atoms_by_domain[p.first]) {
          if (q.first != p.second) {
            // conflict, propagate conflicting_var to false.
            Minisat::Var conflicting_var = q.second;
            Minisat::Lit propagated_lit = ~Minisat::Lit(conflicting_var);
            // TODO HMMM: isn't the direct reason always just the variable we are enabling now???
            Minisat::GClause reason = Minisat::GClause_new(Minisat::Lit(var));
            if (!propagate(propagated_lit, reason)) {
              // Conflict in solver, no use in further propagation
              return;
            }
          }
        }
      }
    }

    /// Undo all assignments above the given level
    void backjump(Level level)
    {
    }
};


}

#endif /* !SUBSTITUTIONTHEORY_HPP */
