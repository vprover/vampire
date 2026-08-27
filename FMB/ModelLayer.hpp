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

#include "Kernel/OperatorType.hpp"
#include "Kernel/Problem.hpp"

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
public:
  explicit TrivialFunLayer(Timestamp born) : FunLayer(LayerKind::TRIVIAL,born) {}

  unsigned value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override
  { return 1; }
};

class TrivialPredLayer : public PredLayer {
public:
  explicit TrivialPredLayer(Timestamp born) : PredLayer(LayerKind::TRIVIAL,born) {}

  char value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override
  { return INTP_FALSE; }
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
public:
  DefFunLayer(Problem::FunDef* fd, Timestamp born) : FunLayer(LayerKind::DEF,born), _fd(fd) {}

  Problem::FunDef* def() const { return _fd; }

  unsigned value(const DArray<unsigned>& args, FiniteModelMultiSorted& m) override;
};

class DefPredLayer : public PredLayer {
  Problem::PredDef* _pd;
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

} // namespace FMB
#endif
