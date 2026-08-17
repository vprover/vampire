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
 * @file ArgsEnumerator.hpp
 * Enumerating argument tuples of FMB interpretation tables
 */

#ifndef __FMB_ArgsEnumerator__
#define __FMB_ArgsEnumerator__

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/OperatorType.hpp"

namespace FMB {

using namespace Lib;
using namespace Kernel;

/**
 * Enumerates all argument tuples (args[0],...,args[arity-1]) with
 * 1 <= args[i] <= bounds[i], the first position changing fastest --
 * which is exactly the row order of the FMB interpretation tables.
 * The empty tuple (arity 0) is enumerated exactly once.
 *
 * Not a Vampire iterator; the intended protocol (do/while, so that the
 * body runs at least once, covering constants and propositions) is:
 *
 *   ArgsEnumerator it(...);
 *   do {
 *     ... use it.args() ...
 *   } while (it.next());
 */
class ArgsEnumerator {
  DArray<unsigned> _bounds;
  DArray<unsigned> _args;

  void initArgs() {
    _args.ensure(_bounds.size());
    for(unsigned i=0;i<_args.size();i++){ _args[i]=1; }
  }
public:
  // bounds[i] = sortSizes[<sort of the i-th argument of ot>]
  ArgsEnumerator(const DArray<unsigned>& sortSizes, OperatorType* ot, unsigned arity)
   : _bounds(arity)
  {
    for(unsigned i=0;i<arity;i++){
      _bounds[i] = sortSizes[ot->arg(i).term()->functor()];
    }
    initArgs();
  }

  // explicitly given bounds
  explicit ArgsEnumerator(DArray<unsigned> bounds) : _bounds(std::move(bounds)) { initArgs(); }

  const DArray<unsigned>& args() const { return _args; }

  /** advance to the next tuple; false (with all args back at 1) when the enumeration wrapped around */
  bool next() {
    unsigned i;
    for(i=0;i<_args.size();i++) {
      _args[i]++;
      if(_args[i] <= _bounds[i]) {
        break;
      }
      _args[i]=1;
    }
    return i != _args.size();
  }

  /** like next(), but also keep subst up to date: subst[vars[i]] == args[i] at every changed position */
  bool nextAndRebind(const DArray<unsigned>& vars, DHMap<unsigned,unsigned>& subst) {
    unsigned i;
    for(i=0;i<_args.size();i++) {
      _args[i]++;
      if(_args[i] <= _bounds[i]) {
        subst.set(vars[i],_args[i]);
        break;
      }
      _args[i]=1;
      subst.set(vars[i],_args[i]);
    }
    return i != _args.size();
  }

  /** set subst[vars[i]] = args[i] for all positions (the initial binding for the nextAndRebind protocol) */
  void bindAll(const DArray<unsigned>& vars, DHMap<unsigned,unsigned>& subst) const {
    for(unsigned i=0;i<_args.size();i++) {
      subst.set(vars[i],_args[i]);
    }
  }
};

} // namespace FMB
#endif
