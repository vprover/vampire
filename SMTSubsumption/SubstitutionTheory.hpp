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
  public:
    /// Decision level in the SAT solver, for backtracking
    using Level = int;

  private:
    /// Maps boolean variables to the theory atoms they represent
    vector_map<Minisat::Var, SubstitutionAtom> atoms;

    /// Maps FOL variables to the list of substitution constraints for this variable
    vector_map<domain, vvector<std::pair<range, Minisat::Var>>> atoms_by_domain;

    // TODO: use this instead of two arrays for current_substitution
    struct SubstEntry {
      range value;
      Level level;
    };

    /// The current substitution.
    /// Maps substitution domain (FOL variables) to substitution range (FOL terms).
    vector_map<domain, range> current_substitution;
    /// Keeps track of the decision level when the current substitution was first set.
    /// If the stored level is larger than the current decision level, the corresponding entry in the current substitution is undefined.
    /// This means when backjumping, we do not have to change anything in current_substitution.
    /// Note that also in other implementations we would need a check whether the entry in current_substitution has been set or not.
    vector_map<domain, Level> current_substitution_level;

  public:
    // empty substitution theory
    SubstitutionTheory()
    { }

    SubstitutionTheory& operator=(SubstitutionTheory&& other) = default;

    explicit
    SubstitutionTheory(SubstitutionTheoryConfiguration&& config)
      : atoms{std::move(config.atoms)}
    {
      // TODO (later):
      // - Do we need to do something about the domain (FOL variables) not being contiguous?
      //   (e.g., there might be a clause with variable X0 and X999 and nothing in between)
      // - A possible way to deal with the situation: add an ImmediateSimplificationRule that normalizes
      //   variable indices whenever max_variable - num_variables > 100 (or another value).
      domain max_d = 0;
      for (auto const& atom : atoms) {
        for (auto const& p : atom.mapping()) {
          max_d = std::max(max_d, p.first);
          ASS(p.second.isNonEmpty());  // we use empty TermLists to mean "unassigned" (TODO: not anymore)
        }
      }
      std::cerr << "max_d = " << max_d << std::endl;

      TermList t_empty;
      t_empty.makeEmpty();
      current_substitution.resize(max_d+1, t_empty);
      // ASS(std::all_of(current_substitution.begin(), current_substitution.end(), [](range t) { return t.isEmpty(); }));
      current_substitution_level.resize(max_d+1, std::numeric_limits<Level>::max());

      atoms_by_domain.resize(max_d+1);
      for (Minisat::Var var = 0; var < atoms.size(); ++var) {
        auto const& atom = atoms[var];
        for (auto const& p : atom.mapping()) {
          std::cerr << "b_" << var << ": " << TermList(p.first, false) << " -> " << p.second << std::endl;
          atoms_by_domain[p.first].push_back({ p.second, var });
        }
      }
    }

    /// Call this when a SAT variable has been set to true
    /// PropagateCallback ~ void(Minisat::Lit propagated,GClause)
    template < typename PropagateCallback >
    void enable(Minisat::Var var, Level level, PropagateCallback propagate)
    {
      std::cerr << "SubstitutionTheory::enable: " << var << " at level " << level << std::endl;
      // Since all our propositional variables have some theory meaning attached,
      // we can assert this.
      // Otherwise we should need whether the variable has some theory component
      // and only proceed if it does.
      ASS_L(var, atoms.size());
      SubstitutionAtom const& atom = atoms[var];
      std::cerr << "atom = " << atom << std::endl;

      // Exhaustively propagate conflicting atoms
      for (auto p : atom.mapping()) {  // go through list of constraints (x -> t)

        if (current_substitution_level[p.first] > level) {
          std::cerr << "Extending current_substitution by " << TermList(p.first, false) << " -> " << p.second << std::endl;
          current_substitution[p.first] = p.second;
          current_substitution_level[p.first] = level;
        } else {
          std::cerr << "Already in current_substitution: " << TermList(p.first, false) << " -> " << current_substitution[p.first] << " from level " << current_substitution_level[p.first] << " (new value: " << p.second  << ")" << std::endl;
          // Must be the same value due to exhaustive theory propagation
          ASS_EQ(current_substitution[p.first], p.second);
          // This also means that all theory consequences have been propagated previously,
          // so we can skip here.
          continue;
        }

        std::cerr << "Propagating theory constraint " << TermList(p.first, false) << " -> " << p.second << "..." << std::endl;

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

            propagate(propagated_lit, reason);
          }
        }
      }

      std::cerr << "enable done" << std::endl;
    }  // enable(...)

    /// Undo all assignments above the given level
    void backjump(Level level)
    {
      // Reset current_substitution
      std::cerr << "BACKJUMP to level " << level << std::endl;
      for (size_t i = 0; i < current_substitution.size(); ++i) {
        if (current_substitution_level[i] > level) {
          current_substitution[i].makeEmpty();
          current_substitution_level[i] = std::numeric_limits<Level>::max();
        }
      }
    }
};


}

#endif /* !SUBSTITUTIONTHEORY_HPP */
