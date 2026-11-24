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
 * @file ModelLayer.cpp
 * What each kind of layer computes (see ModelLayer.hpp).
 *
 * These are here rather than inline in the header because nearly all of them read back into
 * the model -- table indexing, domain sizes, a definition's body, the layer below -- and
 * ModelLayer.hpp can only forward-declare FiniteModelMultiSorted, which includes it.
 * CondFlipPredLayer::value needs nothing from the model and stays inline.
 */

#include <cstdint>

#include "FiniteModelMultiSorted.hpp"
#include "ModelLayer.hpp"

namespace FMB {

// --- explicit tables ---

unsigned TableFunLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  size_t idx = m.tableIndexOf(_sig,args);
  ASS_L(idx,_tbl.size());
  return _tbl[idx]; // FUNV_UNDEF here means the model does not say, and falls through
}

char TablePredLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  size_t idx = m.tableIndexOf(_sig,args);
  ASS_L(idx,_tbl.size());
  return _tbl[idx]; // INTP_UNDEF here means the model does not say, and falls through
}

// --- trivial values, for a symbol nothing constrains ---

#if FMB_CHECK_MODEL_AGAINST_INPUT

// splitmix64's finalizer: cheap, stateless, and it scatters the low bits well enough that
// taking the result modulo a small domain size is not obviously biased
static uint64_t mix(uint64_t x)
{
  x += 0x9e3779b97f4a7c15ull;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ull;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebull;
  return x ^ (x >> 31);
}

// a value determined by the arguments and the symbol's own salt, and by nothing else --
// a trivial layer has to be a function of its arguments like any other interpretation
static uint64_t tupleHash(const DArray<unsigned>& args, unsigned salt)
{
  uint64_t h = salt;
  for(unsigned i=0;i<args.size();i++) {
    h = mix(h ^ args[i]);
  }
  return mix(h);
}

unsigned TrivialFunLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  return 1 + tupleHash(args,_salt) % m.domainSizeOf(_resultSort);
}

char TrivialPredLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  return (tupleHash(args,_salt) & 1) ? INTP_TRUE : INTP_FALSE;
}

#else

unsigned TrivialFunLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  return 1; // an unconstrained symbol may take any value; take the first domain element
}

char TrivialPredLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  return INTP_FALSE;
}

#endif

// --- recorded definitions, and the global flip ---

unsigned DefFunLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  ArgsKey key(args);
  unsigned v;
  if (_memo.find(key,v)) {
    return v;
  }
  v = m.applyFunDef(_fd,args,_born); // the model as it stood when this definition arrived
  _memo.set(key,v); // set, not insert: the evaluation above may have come back round here
  return v;
}

char DefPredLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  ArgsKey key(args);
  char v;
  if (_memo.find(key,v)) {
    return v;
  }
  v = m.applyPredDef(_pd,args,_born) ? INTP_TRUE : INTP_FALSE;
  _memo.set(key,v);
  return v;
}

char GlobalFlipPredLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  // exactly the opposite of what stood below us, and nothing else changes anywhere
  return (m.evalPred(_pred,args,_born) == INTP_TRUE) ? INTP_FALSE : INTP_TRUE;
}

} // namespace FMB
