
/*
 * File MemoryLeak.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file MemoryLeak.hpp
 * Defines the class MemoryLeak used in debugging memory leaks.
 *
 * @since 22/03/2008 Torrevieja
 */


#ifndef __MemoryLeak__
#define __MemoryLeak__

#if CHECK_LEAKS

#include "Allocator.hpp"
#include "Set.hpp"
#include "Hash.hpp"

#include "Kernel/Unit.hpp"

namespace Kernel {
  class Formula;
};

namespace Lib {

class MemoryLeak
{
public:
  void release(Kernel::UnitList*);
  /** Cancel leak report, called when an exception is raised */
  static void cancelReport() { _cancelled = true; }
  /** If true then a report should be made */
  static bool report() { return ! _cancelled; }
private:
  /** If true then no leak reporting is done */
  static bool _cancelled;
  void release(Kernel::Formula*);
  /** Set of generic pointers */
  typedef Set<void*,Hash> PointerSet;
  /** Stores deallocated pointers */
  PointerSet _released;
}; // class MemoryLeak

} // namespace Lib

#endif // CHECK_LEAKS
#endif // __MemoryLeak__
