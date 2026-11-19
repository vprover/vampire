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

namespace Inferences { struct InferenceReplayInformation; }

namespace Lib {

/** Owned proof-extra payload with debug output and optional replay metadata. */
struct InferenceExtra {
  virtual ~InferenceExtra() {};

  /** Replay metadata, if this payload has been replayed. */
  virtual const Inferences::InferenceReplayInformation* replayInformation() const { return nullptr; }

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
 * the old payload. get<T>() requires a compatible payload type. */
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
    return static_cast<T&>(*found);
  }
};
}

#endif
