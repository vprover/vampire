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
 * @file ProofExtra.hpp
 *
 * Include "extra information" about an inference, e.g. selected literals, unifier, etc.
 *
 * @since 09/09/2024 Oxford
 */

#ifndef __Lib_ProofExtra__
#define __Lib_ProofExtra__

#include "Lib/DHMap.hpp"
#include <type_traits>

namespace Lib {

/** Process-local type identity for lookup without RTTI. */
template<class T> const void* inferenceExtraType() {
  static char identity;
  return &identity;
}

/** Owned proof-extra payload with debug output and optional component lookup.
 * Referenced proof objects are borrowed. */
struct InferenceExtra {
  virtual ~InferenceExtra() {};

  /** Find a nested component or composite by type; return a borrowed pointer or nullptr. */
  virtual const void* findComponent(const void*) const { return nullptr; }

  /** Typed lookup; the result shares the payload's lifetime. */
  template<class T> const T* findComponent() const {
    return static_cast<const T*>(findComponent(inferenceExtraType<T>()));
  }

  // for debug printing only, specific output formats should downcast and handle individually
  virtual void output(std::ostream &out) const = 0;

  std::string toString() const {
    std::stringstream ss;
    this->output(ss);
    return ss.str();
  }
};

inline std::ostream &operator<<(std::ostream &out, const InferenceExtra &extra) {
  extra.output(out);
  return out;
}

/** Own extras by proof unit. insert() requires an unused key; replace() discards
 * the old payload. get<T>() requires a matching component or compatible root. */
class ProofExtra {
  DHMap<Kernel::Unit *, std::unique_ptr<InferenceExtra>, UnitHash, UnitNumberHash> extras;

public:
  // associate `extra` with `unit`, taking ownership of `extra`
  void insert(Kernel::Unit *unit, InferenceExtra *extra) {
    ALWAYS(extras.insert(unit, std::unique_ptr<InferenceExtra>(extra)));
  }

  // Commit a complete replay result, replacing any existing extra for the goal.
  void replace(Kernel::Unit *unit, std::unique_ptr<InferenceExtra> extra) {
    ASS(extra);
    extras.set(unit, std::move(extra));
  }

  // remove the extra information for this unit
  void remove(Kernel::Unit *unit) {
    extras.remove(unit);
  }

  // associated InferenceExtra if present, nullptr otherwise
  const InferenceExtra *find(const Kernel::Unit *unit) {
    auto *found = extras.findPtr(const_cast<Kernel::Unit *>(unit));
    if(!found)
      return nullptr;
    return found->get();
  }

  // associated InferenceExtra: must be present
  template<typename T>
  T &get(Kernel::Unit *unit) {
    auto &found = extras.get(unit);
    ASS(found)
    auto* component = found->findComponent<T>();
    if constexpr (std::is_base_of_v<InferenceExtra, T>) {
      if (!component) { return static_cast<T &>(*found); }
    }
    ASS(component);
    return *const_cast<T*>(component);
  }
};
}

#endif
