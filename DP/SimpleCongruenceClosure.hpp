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
 * @file SimpleCongruenceClosure.hpp
 * Defines class SimpleCongruenceClosure for implementing congruence closure
 */

#ifndef __SimpleCongruenceClosure__
#define __SimpleCongruenceClosure__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Deque.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Ordering.hpp"

#include "DecisionProcedure.hpp"

namespace DP {

using namespace Lib;
using namespace Kernel;

/**
 * Implementation of congruence closure.
 * 
 * Martin: seems to be inspired Nieuwenhuis, Oliveras (2007) Fast Congruence Closure and Extensions
 * (at least the congruence closure itself and also the proof recording
 * explanations [the unsat core extraction] seem to be simpler and suboptimal 
 * -- the HighestNode trick ? )
 * 
 * Hint: understand _pairNames as "Lookup" from the paper.
 * 
 * However, classList of a representative 
 * does not (physically) contain that representative (only logically)
 */
class SimpleCongruenceClosure : public DecisionProcedure
{
public:
  CLASS_NAME(SimpleCongruenceClosure);
  USE_ALLOCATOR(SimpleCongruenceClosure);

  SimpleCongruenceClosure(Ordering* ord);

  virtual void addLiterals(LiteralIterator lits, bool onlyEqualites) override;

  virtual Status getStatus(bool retrieveMultipleCores) override;
  virtual unsigned getUnsatCoreCount() override { return _unsatEqs.size(); }
  virtual void getUnsatCore(LiteralStack& res, unsigned coreIndex) override;

  void getModel(LiteralStack& model) override;
  
  virtual void reset() override;

  /**
   * New, more fine-grained way of insertion. The terms may contain variables which are treated as constants.
   */
  void addLiteral(Literal* lit);

  /**
   * After a call to getStatus (and before reset)
   * this function returns a class id representing a given term.
   *
   * The term must have been a sub-term (not necessarily proper)
   * of some of the terms in the input.
   */
  unsigned getClassID(TermList t) {
    return deref(_termNames.get(t));
  }

private:
  Ordering* _ord;
  
  /**
   * Constant pair
   *
   * Is used for the shallow representation of the currifyed terms.
   */
  typedef pair<unsigned,unsigned> CPair;
  /** Equality between two constants */
  struct CEq
  {
    CEq() : c1(0), c2(0), foOrigin(false), foPremise(nullptr) {}
    CEq(unsigned c1, unsigned c2, Literal* lit)
     : c1(c1), c2(c2), foOrigin(true), foPremise(lit) {}
    CEq(unsigned c1, unsigned c2)
     : c1(c1), c2(c2), foOrigin(false), foPremise(nullptr) {}

    bool isInvalid() const { ASS_EQ(c1==0, c2==0); return c1==0; }
    vstring toString() const;
    vstring toString(SimpleCongruenceClosure& parent) const;

    unsigned c1;
    unsigned c2;
    /**
     * If true, equality comes from @c foPremise, if false,
     * it follows from a congruence between pairs represented by
     * @c c1 and @c c2.
     */
    bool foOrigin;
    /** if 0, the equality is the true!=false equality to help represent non-equality literals */
    Literal* foPremise;

  };

  enum class SignatureKind {
    PREDICATE,
    FUNCTION,
    TYPECON,
    VARIABLE
  };

  unsigned getMaxConst() const { return _cInfos.size()-1; }
  unsigned getFreshConst();
  unsigned getSignatureConst(unsigned symbol, SignatureKind kind);
  unsigned getPairName(CPair p);


  struct FOConversionWorker;
  static bool isDistinctPred(Literal* l);
  CEq convertFOEquality(Literal* equality);
  unsigned convertFONonEquality(Literal* lit);
  unsigned convertFO(TermList trm);
  void readDistinct(Literal* lit);


 /**
  * Get the representative constant for constant @c
  * i.e. the representative for its congruence class
  */
  unsigned deref(unsigned c) const {
    CALL("SimpleCongruenceClosure::deref");
    unsigned repr = _cInfos[c].reprConst;
    unsigned res = (repr==0) ? c : repr;
    ASS_REP2(_cInfos[res].reprConst==0, _cInfos[res].reprConst, c);
    return res;
  }
 /**
  * Get a CPair of constants from a CPair by deref-ing each half of the pair
  */
  CPair deref(CPair p) const { return CPair(deref(p.first), deref(p.second)); }
 /**
  * Get a CPair of constants from a CEq by deref-ing each half
  */
  CPair deref(CEq p) const { return CPair(deref(p.c1), deref(p.c2)); }

  unsigned getClassSize(unsigned c) const {
    return _cInfos[c].classList.size();
  }

  bool checkPositiveDistincts(bool retrieveMultipleCores);
  Status checkNegativeDistincts(bool retrieveMultipleCores);

  void addPendingEquality(CEq eq);
  void makeProofRepresentant(unsigned c);
  void propagate();

  unsigned getProofDepth(unsigned c);
  void collectUnifyingPath(unsigned c1, unsigned c2, Stack<unsigned>& path);

  static const unsigned NO_SIG_SYMBOL;
  struct ConstInfo
  {
    void init();
    void resetEquivalences(SimpleCongruenceClosure& parent, unsigned selfIndex);

#if VDEBUG
    void assertValid(SimpleCongruenceClosure& parent, unsigned selfIndex) const;
#endif

    /** If NO_SIG_SYMBOL, the constant doesn't represent a non-constant signature symbol */
    unsigned sigSymbol;
    SignatureKind sigSymKind;
    /** If isEmpty, the constant doesn't represent a term */
    TermList term;
    /** If non-zero, constant stands for a non-equality atom */
    Literal* lit;
    /** (0,0) means the constant doesn't name a pair */
    CPair namedPair;

    /** 0 means the symbol is its own representative */
    unsigned reprConst;

    /**
     * A parent in an union-find structure without path-compression
     *
     * (used for proof construction)
     */
    unsigned proofPredecessor;
    /**
     * Premise that justified union with proofPredecessor
     */
    CEq predecessorPremise;


    /** If reprConst==0, contains other constants whose representative
     * this constant is */
    Stack<unsigned> classList;
    /**
     * If reprConst==0, contains list of pair names in whose pairs this
     * constant appears as a representative of one of the arguments.
     * Irregardless of the value of reprConst, also contains representatives
     * of all pairs that have this very constant as one of arguments.
     */
    Stack<unsigned> useList;
        
    // needed for getModel:    
    /**
     * Meaningful for representatives. Marking processed classes.
     */
    bool processed;
    /**
     * Meaningful for representatives. A list of edges leaving the class "upwards".
     */
    Stack<unsigned> upEdges;
    /**
     * Meaningful for namedPairs. 
     * 
     * One of the arguments have been normalized.
     * When we learn about the other, we put it to potential candidates.
     */
    bool half_normalized;
    
    /**
     * Meaningful for classes which represent a FO term (not just a partial application).
     * 
     * Consists of the original term's function symbol and normalised
     * sub-terms obtained by replacing the original sub-term by its class's
     * representative's normal form.
     */
    TermList normalForm;    
  };

  struct ConstOrderingComparator;  
  typedef DHMap<unsigned,TermList> NFMap;
  void computeConstsNormalForm(unsigned c, NFMap& normalForms);
  
#if VDEBUG
  void assertModelInfoClean() const;
#endif  
  
  /**
   * Information on constants used in the algorithm
   *
   * The element at index 0 is ignored, as number 0 is used in place
   * of constants in special cases, such as to indicate that there is
   * no constant.
   */
  DArray<ConstInfo> _cInfos;

  /** Positive literals are made equivalent to this constant */
  unsigned _posLitConst;
  /** Negative literals are made equivalent to this constant */
  unsigned _negLitConst;

  /**
   * Map from signature symbols to the local constant numbers.
   */
  DHMap<pair<unsigned,SignatureKind>,unsigned> _sigConsts;

  typedef DHMap<CPair,unsigned> PairMap;
  /** Names of constant pairs (modulo the congruence!)*/
  PairMap _pairNames;

  /** Constants corresponding to terms */
  DHMap<TermList,unsigned> _termNames;
  /** Constants corresponding to literals */
  DHMap<Literal*,unsigned> _litNames;

  /**
   * Equality that caused unsatisfiability; if CEq::isInvalid(), there isn't such.
   */
  Stack<CEq> _unsatEqs;
  Deque<CEq> _pendingEqualities;
  Stack<CEq> _negEqualities;

  struct DistinctEntry
  {
    DistinctEntry(Literal* l) : _lit(l) {}
    Literal* _lit;
    Stack<unsigned> _consts;
  };
  typedef Stack<DistinctEntry> DistinctStack;
  DistinctStack _distinctConstraints;
  /** Negated distinct constraints, these can lead to an UNKNOWN satisfiability result 
   * 
   * Martin: Strictly speaking these are not part of TPTP: 
   * http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html
   * "It can be used only as a fact, not under any connective." */  
  DistinctStack _negDistinctConstraints;

  /**
   * used to assert we don't add literals after propagation.
   * this would cause problems with term caches upon reset.
   */
  bool _hadPropagated;
}; // class SimpleCongruenceClosure

}

#endif // __SimpleCongruenceClosure__
