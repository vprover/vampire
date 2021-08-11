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
 * @file Saturation/ProofTracer.hpp
 * Defines class ProofTracer.
 */

#ifndef __Saturation_ProofTracer__
#define __Saturation_ProofTracer__

#include "Forwards.hpp"

#include "Parse/TPTP.hpp"
#include "Indexing/ClauseVariantIndex.hpp"
#include "Kernel/RCClauseStack.hpp"

namespace Saturation {

struct ProofTracer {
  USE_ALLOCATOR(ProofTracer);

  // helper functions and subclasses

  static void printWithStore(Clause* cl) {
    std::cout << cl->store() << " " << cl->toString() << std::endl;
    if (cl->store() == Clause::PASSIVE && cl->getPassiveDist()) {
      std::cout << "distance: " << cl->getPassiveDist() << " age: " << cl->age() << " weight: " << cl->weightForClauseSelection(*env.options) << std::endl;
    }
  }

  enum InferenceKind {
    ICP = 0, // INPUT / PREPROCESSING / CLAUSIFICATION anything larger than this should end up in the TracedProof
    TRIVSIMP = 1,
    DUPLELIM = 2, // DUPLICAT_LITERAL_ELIMINATION is problematic as our variant index does not correctly retrieve duplicate literal clauses;
      // to make up for this, we ``edit out'' DUPLELIM inference both from the TracedProof and later on, online, pretend it does no happen also when clauses arrive
    SIMPLIFYING = 3,  // TODO: let's see whether we don't also need to distinguish FWD and BWD!
    GENERATING = 4,
  };

  /* a temporary struct we get from parsing the TPTP proof file; becomes obsolete once we get a TracedProof object out of it */
  struct ParsedProof {
    USE_ALLOCATOR(ParsedProof);

    UnitList* units;
    DHMap<unsigned, vstring> names;
    DHMap<Unit*,Parse::TPTP::SourceRecord*> sources;
  };

  struct TracedClauseInfo {
    USE_ALLOCATOR(TracedClauseInfo);

    vstring _name;     // the Unit::number of the clause in the original derivation
    vstring _inf;      // the name of the inference as read from the original derivation file
    InferenceKind _ik; // the kind of inference this clause arose by

    unsigned _num;     // assigned when first stalkee is registered
    bool _exacted;     // found a stalkee whose parents are matched by the original parents of this clause (and those were also exacted at the moment this happened)
                       // when we don't exact a clause with the first stalkee, we still move the exacting stalkee to be the first one!

    TracedClauseInfo(const vstring& name, const vstring& inf, InferenceKind ik) : _name(name), _inf(inf), _ik(ik),
        _num(0), _exacted(false),
        _numAwokenParents(0) {}

    Stack<Clause*> _parents;  // premises
    Stack<Clause*> _children; // the opposite arrows

    bool isInital() {
      return _parents.size() == 0;
    }

    // should be only the final empty clause
    bool isTerminal() {
      return _children.size() == 0;
    }

    // the clause(s) from the new run we think should play the same role in the new proof
    RCClauseStack _stalkees;

    unsigned _numAwokenParents;
  };

  struct TracedProof {
    USE_ALLOCATOR(TracedProof);

    void init();

    // events from Tracer mapped to (each) TracedProof

    void onNewClause(Clause* cl);
    void onInputClause(Clause* cl);
    void onInputFinished();
    void onPassiveNumbered();
    void onActivation(Clause* cl);
    void onActivationFinished(Clause* cl);
    void onSaturationFinished();

    // aux:

    void regNewClause(Clause* cl, const vstring& name, const vstring& inf, InferenceKind ik) {
      ALWAYS(_clInfo.insert(cl,new TracedClauseInfo(name,inf,ik)));

      _variantLookup->insert(cl);

      ClauseList::push(cl,_inOrder);
    }

    TracedClauseInfo* getInfo(Clause* cl) {
      return _clInfo.get(cl);
    }

    void regChildParentPair(Clause* ch, Clause* p) {
      _clInfo.get(ch)->_parents.push(p);
      _clInfo.get(p)->_children.push(ch);
    }

    void setEmpty(Clause* cl) {
      ASS_EQ(_theEmpty,0); // only set once
      _theEmpty = cl;
    }

    Clause* findVariant(Clause* cl) {
      Clause* res = 0;

      ClauseIterator it = _variantLookup->retrieveVariants(cl);
      if (it.hasNext()) {
        res = it.next();
        ASS(!it.hasNext());
      }
      return res;
    }

    void listExpecteds();
    void listExpectedsDetails();

    TracedProof() : _seen(0), _inOrder(nullptr), _theEmpty(0), _variantLookup(new Indexing::HashingClauseVariantIndex()),
        _numInitials(0), _seenInitials(0), _lastActivationMatch(0) {}
    ~TracedProof() { delete _variantLookup; }

  private:
    unsigned _seen;

    ClauseList* _inOrder;

    Clause* _theEmpty;
    DHMap<Clause*, TracedClauseInfo*> _clInfo;

    Indexing::ClauseVariantIndex* _variantLookup;

    unsigned _numInitials;
    unsigned _seenInitials;

    Clause* _lastActivationMatch;

    /* Set of clauses that are expected to appear as their parents (in the traced proof)
     *  have already been spotted.
     *  (Could start with all the initial clauses in expecting, but those are already taken care of by the _unbornInitials counter.)
     **/
    DHSet<Clause*> _expecting;
  };

  /**
   * Initialize the ProofTracer by reading some proofs from the given file (traceFileNames).
   * (Tracing of more than one proof is envisaged for the future
   * but currently only one proof file is supported.)
   *
   * Note: To produce a loadable proof run vampire with "-p tptp" (and consider adding "--output_axiom_names on")
   */
  void init(const vstring& traceFileNames);

  /**
   * Various events by which SaturationAlgorithm notifies the tracer about clause happenings.
   *
   * On onNewClause uses variant index to match up a clause from the traced proof with the newly derived.
   * Other events may only respond to already matched up clauses (ASS(cl->isTraced())).
   *
   * The main idea behind events is to be able to identify and report as soon as possible
   * that a particular expected inference will not happen in the new saturation (the way it happened in the old one).
   *
   * For instance, if we haven't seen all the expected input clauses by the time onInputFinished is called,
   * there is no chance to flawlessly trace the original proof anymore (as some of the required initial clauses is now known to be missing).
   */

  void onNewClause(Clause* cl)
  {
    _tp->onNewClause(cl);
  }
  void onInputClause(Clause* cl)
  {
    _tp->onInputClause(cl);
  }

  void onInputFinished()
  {
    _tp->onInputFinished();
  }

  void onPassiveNumbered()
  {
    _tp->onPassiveNumbered();
  }

  void onActivation(Clause* cl)
  {
    _tp->onActivation(cl);
  }
  void onActivationFinished(Clause* cl)
  {
    _tp->onActivationFinished(cl);
  }

  void onSaturationFinished()
  {
    _tp->onSaturationFinished();
  }

  ParsedProof* getParsedProof(const vstring& traceFileNames);
  TracedProof* prepareTracedProof(ParsedProof* pp);
  void initializeTracedProof(TracedProof* tp);

  ProofTracer() : _tp(0) {}

private:
  TracedProof* _tp;

  Clause* unitToClause(Unit* u);
};

}

#endif // __Saturation_ProofTracer__
