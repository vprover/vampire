/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_Inferences_TautologyDeletion__
#define __ALASCA_Inferences_TautologyDeletion__

#include "Forwards.hpp"

#include "Kernel/ALASCA.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class TautologyDeletion
: public ImmediateSimplificationEngine
{
  std::shared_ptr<AlascaState> _shared;
public:
  USE_ALLOCATOR(TautologyDeletion);

  TautologyDeletion(std::shared_ptr<AlascaState> shared) 
    : _shared(std::move(shared)) {}

  Clause* simplify(Clause* premise) override 
  {
    Map<AnyAlascaLiteral, bool> lits;
    TIME_TRACE("alasca tautology detection")
    for (auto lit : iterTraits(premise->iterLits())) {
      auto norm_ = _shared->norm().tryNormalizeInterpreted(lit);
      if (norm_.isSome()) {
        auto norm = norm_.unwrap();
        lits.insert(norm, true);
        auto opposite = norm.apply([&](auto lit) { return AnyAlascaLiteral(lit.negation()); });
        if (lits.find(opposite)) {
          // std::cout << "bla" << std::endl;
          return nullptr;
        }
      }
    }

    return premise;
  }
};

#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_TautologyDeletion__*/
