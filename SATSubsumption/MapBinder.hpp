#ifndef SMTSUBSUMPTION_MAPBINDER_HPP
#define SMTSUBSUMPTION_MAPBINDER_HPP


#include "Kernel/Term.hpp"
#include "Lib/STL.hpp"

namespace SMTSubsumption {

using namespace Kernel;

class MapBinderVampire
{
  CLASS_NAME(MapBinderVampire);
  USE_ALLOCATOR(MapBinderVampire);

public:
  using Var = unsigned int;
  using BindingsMap = DHMap<Var, TermList, IdentityHash>;

  MapBinderVampire()
  { }

  bool bind(Var var, TermList term)
  {
    TermList* aux;
    return m_bindings.getValuePtr(var, aux, term) || *aux == term;
  }

  void specVar(unsigned var, TermList term)
  {
    ASSERTION_VIOLATION;
  }

  void reset()
  {
    m_bindings.reset();
  }

  BindingsMap const& bindings() const
  {
    return m_bindings;
  }

  size_t size() const
  {
    return m_bindings.size();
  }

private:
  BindingsMap m_bindings;
};

/**
 * This class implements the Binder interface as described in Kernel/Matcher.hpp.
 * Does not support special variables.
 */
class MapBinderSTL
{
  CLASS_NAME(MapBinderSTL);
  USE_ALLOCATOR(MapBinderSTL);

  public:
    using Var = unsigned int;
    struct VarIdentityHash {
      std::size_t operator() (Var v) const {
        return v;
      }
    };
    using BindingsMap = vunordered_map<Var, TermList, VarIdentityHash>;  // slow!

    MapBinderSTL()
      : m_bindings(16)
    { }

    explicit
    MapBinderSTL(BindingsMap&& bindings)
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

    size_t size() const
    {
      return m_bindings.size();
    }

  private:
    BindingsMap m_bindings;

    friend std::ostream& operator<<(std::ostream&, MapBinderSTL const&);
};  // class MapBinder


std::ostream& operator<<(std::ostream&, MapBinderSTL const&);


using MapBinder = MapBinderVampire;


}

#endif /* !SMTSUBSUMPTION_MAPBINDER_HPP */
