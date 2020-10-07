/*
 * MapBinder.hpp
 * Copyright (C) 2020 Jakob Rath <git@jakobrath.eu>
 *
 * Distributed under terms of the MIT license.
 */

#ifndef SMTSUBSUMPTION_MAPBINDER_HPP
#define SMTSUBSUMPTION_MAPBINDER_HPP


#include "Kernel/Term.hpp"
#include "Lib/STL.hpp"

namespace SMTSubsumption {

using namespace Kernel;


/**
 * This class implements the Binder interface as described in Kernel/Matcher.hpp.
 */
class MapBinder
{
  CLASS_NAME(MapBinder);
  USE_ALLOCATOR(MapBinder);

  public:
    using Var = unsigned int;
    using BindingsMap = vunordered_map<Var, TermList>;

    MapBinder()
      : m_bindings(16)
    { }

    explicit
    MapBinder(BindingsMap&& bindings)
      : m_bindings(std::move(bindings))
    { }

    bool bind(Var var, TermList term)
    {
      auto result = m_bindings.insert({var, term});
      auto it = result.first;
      bool inserted = result.second;
      // If the variable is already bound, it must be bound to the same term.
      return inserted || (it->second == term);
    }

    void specVar(Var var, TermList term)
    {
      ASSERTION_VIOLATION;
    }

    void reset()
    {
      m_bindings.clear();
    }

    BindingsMap const& bindings() const
    {
      return m_bindings;
    }

  private:
    BindingsMap m_bindings;

    friend std::ostream& operator<<(std::ostream&, MapBinder const&);
};  // class MapBinder


std::ostream& operator<<(std::ostream&, MapBinder const&);


}

#endif /* !SMTSUBSUMPTION_MAPBINDER_HPP */
