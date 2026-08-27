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
 * @file ModelLayer.hpp
 * One version of one symbol's interpretation in a finite model.
 *
 * The transformations preprocessing applied to a problem are undone one by one when a model
 * of the preprocessed problem is turned back into a model of the original one (see
 * FiniteModelMultiSorted::restoreEliminatedDefinitions). That replay is a *sequence of
 * models* -- model_0, model_1, ... -- in which model_j is defined in terms of model_{j-1}.
 *
 * So a symbol's interpretation is not a single object that gets overwritten; it is a stack of
 * layers, one per replay step that had something to say about that symbol. Reading the model
 * means walking the stack from the top and taking the first layer that has a value for the
 * arguments at hand -- a layer with nothing to say (an explicit table with a hole, a
 * conditional flip that does not cover these arguments) simply falls through to the one below.
 */

#ifndef __FMB_ModelLayer__
#define __FMB_ModelLayer__

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/Problem.hpp"

// Temporary, assert-like sanity instrument: when 1, a single-strategy fmb run snapshots the
// parsed input (see preprocessProblem in vampire.cpp) and, at the end of onModelFound,
// checks the constructed model against it -- a false original unit raises USER_ERROR.
// It also makes the trivial layers below pick pseudo-random values rather than a fixed one.
// To be set to 0 (or removed) once the symbolic-definitions work has been stress-tested;
// it lives here because this is the lowest header that has to see it.
#define FMB_CHECK_MODEL_AGAINST_INPUT 1

namespace FMB {

using namespace Lib;
using namespace Kernel;

class FiniteModelMultiSorted;

/**
 * When a layer was created: the replay step that pushed it, counting model_0 as 0. A layer
 * reads the model *as of* a timestamp -- it sees exactly the layers born strictly earlier --
 * which is what keeps model_j defined in terms of model_{j-1} and nothing later.
 */
using Timestamp = unsigned;

// the timestamp of model_0, the model the replay starts from
inline constexpr Timestamp MODEL_ZERO = 0;

// what a predicate table cell holds; INTP_UNDEF doubles as "ask the layer below"
inline constexpr char INTP_UNDEF = 0;
inline constexpr char INTP_FALSE = 1;
inline constexpr char INTP_TRUE  = 2;

// the corresponding "ask the layer below" for a function is 0, which is not a domain
// element (those are 1-based)
inline constexpr unsigned FUNV_UNDEF = 0;

enum class LayerKind : unsigned char {
  TABLE,        // the interpretation given cell by cell
  TRIVIAL,      // an implicitly eliminated symbol, free to take any value
  DEF,          // a recorded definition, evaluated on demand
  GLOBAL_FLIP,  // the negation of the layer below
  COND_FLIP,    // the layer below, overridden on the argument tuples a condition selected
};

struct FunLayer {
  const LayerKind _kind;
  const Timestamp _born;
  FunLayer(LayerKind kind, Timestamp born) : _kind(kind), _born(born) {}
  virtual ~FunLayer() {}

  /** the value at args, or FUNV_UNDEF to mean "nothing to say here; ask the layer below" */
  virtual unsigned value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) = 0;
};

struct PredLayer {
  const LayerKind _kind;
  const Timestamp _born;
  PredLayer(LayerKind kind, Timestamp born) : _kind(kind), _born(born) {}
  virtual ~PredLayer() {}

  /** the value at args, or INTP_UNDEF to mean "nothing to say here; ask the layer below" */
  virtual char value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) = 0;
};

/**
 * The interpretation given explicitly, one cell per argument tuple, addressed by the
 * encoding tableIndex describes. This is what the SAT solver's assignment is copied into.
 */
class TableFunLayer : public FunLayer {
  OperatorType* _sig;
  DArray<unsigned> _tbl;
public:
  TableFunLayer(OperatorType* sig, size_t rows, Timestamp born)
   : FunLayer(LayerKind::TABLE,born), _sig(sig)
  { _tbl.expand(rows,FUNV_UNDEF); }

  OperatorType* sig() const { return _sig; }
  DArray<unsigned>& raw() { return _tbl; }

  unsigned value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override;
};

class TablePredLayer : public PredLayer {
  OperatorType* _sig;
  DArray<char> _tbl;
public:
  TablePredLayer(OperatorType* sig, size_t rows, Timestamp born)
   : PredLayer(LayerKind::TABLE,born), _sig(sig)
  { _tbl.expand(rows,INTP_UNDEF); }

  OperatorType* sig() const { return _sig; }
  DArray<char>& raw() { return _tbl; }

  char value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override;
};

/**
 * A symbol nothing in the model constrains: it disappeared during preprocessing without any
 * step recording what it should be (its last occurrence went away with some other
 * elimination), so it is free to take any value at all. Taking the first domain element for a
 * function and $false for a predicate is as good a choice as any.
 *
 * Every symbol without an explicit table gets one of these at the bottom of its stack, which
 * is what makes model_0 total -- and hence what lets a later step be a *correction* to a
 * model that already says something everywhere, rather than a definition of a partial one.
 */
class TrivialFunLayer : public FunLayer {
#if FMB_CHECK_MODEL_AGAINST_INPUT
  // Under the self-check the arbitrary value is deliberately *not* a constant: "arbitrary"
  // is a claim about the model being free here, and picking the same element everywhere is
  // the one choice least likely to expose a symbol that is not in fact free. The salt makes
  // it pseudo-random junk instead, reproducible for a given -random_seed. Everything about
  // this is compiled out when the self-check is; the layer is then simply "the first element".
  unsigned _resultSort;
  unsigned _salt;
public:
  TrivialFunLayer(unsigned resultSort, unsigned salt, Timestamp born)
   : FunLayer(LayerKind::TRIVIAL,born), _resultSort(resultSort), _salt(salt) {}
#else
public:
  explicit TrivialFunLayer(Timestamp born) : FunLayer(LayerKind::TRIVIAL,born) {}
#endif

  unsigned value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override;
};

class TrivialPredLayer : public PredLayer {
#if FMB_CHECK_MODEL_AGAINST_INPUT
  unsigned _salt; // see TrivialFunLayer
public:
  TrivialPredLayer(unsigned salt, Timestamp born)
   : PredLayer(LayerKind::TRIVIAL,born), _salt(salt) {}
#else
public:
  explicit TrivialPredLayer(Timestamp born) : PredLayer(LayerKind::TRIVIAL,born) {}
#endif

  char value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override;
};

/**
 * An argument tuple, used as a hash-map key.
 *
 * Deliberately not the flat table index: tableIndex multiplies out the domain sizes with no
 * overflow check (only tableSize has one, and a conditional flip is exactly the place where a
 * symbol's table is never built), so two distinct tuples of a wide enough symbol would alias.
 * Hashing the values also keeps the layout run-to-run stable, unlike hashing an address.
 */
class ArgsKey {
  DArray<unsigned> _args;
public:
  ArgsKey() {}
  explicit ArgsKey(const DArray<unsigned>& args) : _args(args.clone()) {}

  // DArray only move-assigns (its operator= swaps), so spell the copies out; DHMap stores
  // its keys by value and reassigns them when it grows
  ArgsKey(const ArgsKey& o) : _args(o._args.clone()) {}
  ArgsKey& operator=(const ArgsKey& o) { _args = o._args.clone(); return *this; }
  ArgsKey(ArgsKey&&) = default;
  ArgsKey& operator=(ArgsKey&&) = default;

  bool operator==(const ArgsKey& o) const
  {
    if (_args.size() != o._args.size()) {
      return false;
    }
    for (unsigned i = 0; i < _args.size(); i++) {
      if (_args[i] != o._args[i]) return false;
    }
    return true;
  }
  bool operator!=(const ArgsKey& o) const { return !(*this == o); }

  unsigned defaultHash() const
  {
    unsigned h = 1;
    for (unsigned i = 0; i < _args.size(); i++) { h = HashUtils::combine(h,_args[i]); }
    return h;
  }
  unsigned defaultHash2() const
  {
    unsigned h = 17;
    for (unsigned i = 0; i < _args.size(); i++) { h = HashUtils::combine(_args[i],h); }
    return h;
  }
};

/**
 * A definition recorded when preprocessing eliminated the symbol: the head is linear in its
 * variables, and the body is a term (or formula) over the symbols that were still live at
 * that point.
 *
 * The body is evaluated as of the layer's own birth, i.e. in the model this replay step
 * transforms -- never in the model as it ends up. That is what the timestamps are for. It is
 * also what makes the definition agree with the problem it came from: the body's symbols are
 * the ones that step saw, and a flip replayed afterwards is undoing a *later* preprocessing
 * step, whose effect the body's own problem still had.
 *
 * The definition object belongs to Problem::interferences; the layer only points at it.
 */
class DefFunLayer : public FunLayer {
  Problem::FunDef* _fd;
  // Evaluating a body is not cheap -- bodies nest, and an eliminated predicate's body is a
  // disjunction with existential prefixes -- while the answer never changes: everything the
  // body reads is born before this layer and so is already fixed. Remembering the answers is
  // what materialization used to provide as a side effect of writing a table, except that
  // this costs one entry per argument tuple actually asked about rather than per tuple that
  // exists.
  DHMap<ArgsKey,unsigned> _memo;
public:
  DefFunLayer(Problem::FunDef* fd, Timestamp born) : FunLayer(LayerKind::DEF,born), _fd(fd) {}

  Problem::FunDef* def() const { return _fd; }

  unsigned value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override;
};

class DefPredLayer : public PredLayer {
  Problem::PredDef* _pd;
  DHMap<ArgsKey,char> _memo; // see DefFunLayer
public:
  DefPredLayer(Problem::PredDef* pd, Timestamp born) : PredLayer(LayerKind::DEF,born), _pd(pd) {}

  Problem::PredDef* def() const { return _pd; }

  char value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override;
};

/**
 * Polarity flipping (Shuffling::polarityFlip, under -random_polarities) replaced a predicate
 * by its negation throughout the problem, so undoing it means negating the model on that
 * predicate -- and on nothing else. As a layer that is literally what it says: read the layer
 * below and return the opposite.
 *
 * "Below" is as of this layer's own birth, which is what confines the change to this symbol.
 * A definition elsewhere whose body reads the flipped predicate was born earlier and so
 * cannot see this layer at all; one born later is meant to see it.
 */
class GlobalFlipPredLayer : public PredLayer {
  unsigned _pred;
public:
  GlobalFlipPredLayer(unsigned pred, Timestamp born)
   : PredLayer(LayerKind::GLOBAL_FLIP,born), _pred(pred) {}

  char value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override;
};

/**
 * A conditional flip prescribes the predicate's value on just the argument tuples its
 * condition selects, and leaves it alone everywhere else -- which is a sparse map over a
 * fall-through, not a rewritten table. That is the whole reason this can be a layer at all:
 * a predicate of arity 47 over a two-element domain has no table we could afford, but the
 * handful of tuples a flip actually touches costs nothing.
 *
 * The value is stored, not just the fact that a flip happened, so a hit needs no second
 * lookup and the layer need not remember which way it flipped.
 */
class CondFlipPredLayer : public PredLayer {
  DHMap<ArgsKey,char> _vals;
public:
  explicit CondFlipPredLayer(Timestamp born) : PredLayer(LayerKind::COND_FLIP,born) {}

  char value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override
  {
    char v;
    return _vals.find(ArgsKey(args),v) ? v : INTP_UNDEF; // no entry: whatever is below stands
  }

  void prescribe(const DArray<unsigned>& args, char val) { _vals.set(ArgsKey(args),val); }
};

} // namespace FMB
#endif
