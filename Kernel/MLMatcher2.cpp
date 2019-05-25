/*
 * File MLMatcher2.cpp.
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
 * @file MLMatcher2.cpp
 * Implements class MLMatcher2.
 */

#include <algorithm>

#include "Lib/BinaryHeap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Hash.hpp"
#include "Lib/TriangularArray.hpp"

#include "Clause.hpp"
#include "Matcher.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "MLMatcher2.hpp"

#if VDEBUG
#include <iostream>
#include "Test/Output.hpp"
#endif


namespace {

using namespace Lib;
using namespace Kernel;


typedef DHMap<unsigned,unsigned, IdentityHash> UUMap;


/**
 * Binder that stores bindings into a specified array. To be used
 * with MatchingUtils template methods.
 */
struct ArrayStoringBinder
{
  ArrayStoringBinder(TermList* arr, UUMap& v2pos)
    : _arr(arr), _v2pos(v2pos) {}

  bool bind(unsigned var, TermList term)
  {
    _arr[_v2pos.get(var)]=term;
    return true;
  }

  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }
private:
  TermList* _arr;
  UUMap& _v2pos;  // Maps variable to array position
};


/**
 * Compute and store variable bindings that instantiate baseLit to alt, for each alternative alt in the list alts.
 * The result of this function is independent of the current matching state.
 *
 * @param baseLit The base literal.
 * @param alts The list of alternatives that baseLit can be matched to.
 * @param instCl The instance clause. All alternatives must be part of this clause.
 * @param boundVarData The variables occurring in baseLit will be added to this array in ascending order. Needs to point to a large enough array.
 * @param altBindingPtrs For each match of baseLit to an alt, will add one pointer to altBindingPtrs. Indicates the first element of altBindingData that is associated with this alt.
 * @param altBindingData Will contain the actual variable bindings. For each variable in baseLit in ascending order, the array will contain the term bound to that variable.
 *                       Furthermore, in an additional last position it will contain the index of the alternative in instCl.
 *
 * Why do we pass these weird references to pointers?
 * => It allows us to create a single linear array at the beginning of matcher initialization, and thus avoids many small dynamic allocations.
 */
bool createLiteralBindings(Literal* baseLit, LiteralList* alts, Clause* instCl, unsigned*& boundVarData, TermList**& altBindingPtrs, TermList*& altBindingData)
{
  CALL("createLiteralBindings");

  static UUMap variablePositions;
  static BinaryHeap<unsigned,Int> varNums;
  variablePositions.reset();
  varNums.reset();

  VariableIterator bvit(baseLit);
  while(bvit.hasNext()) {
    unsigned var=bvit.next().var();
    varNums.insert(var);
  }

  // Add (unique) variables in baseLit to boundVarData in ascending order.
  // At the same time, fill the map variablePositions which maps each variable to its position in this sorted sequence.
  unsigned nextPos=0;
  while(!varNums.isEmpty()) {
    unsigned var=varNums.pop();
    while(!varNums.isEmpty() && varNums.top()==var) {
      varNums.pop();
    }
    if(variablePositions.insert(var,nextPos)) {
      *(boundVarData++)=var;
      nextPos++;
    }
  }
  unsigned numVars=nextPos;

  LiteralList::Iterator ait(alts);
  while(ait.hasNext()) {
    Literal* alit=ait.next();
    if(alit->isEquality()) {
      //we must try both possibilities
      if(MatchingUtils::matchArgs(baseLit,alit)) {
        ArrayStoringBinder binder(altBindingData, variablePositions);
        MatchingUtils::matchArgs(baseLit,alit,binder);
        *altBindingPtrs=altBindingData;
        altBindingPtrs++;
        altBindingData+=numVars;
        // add index of the literal in instance clause at the end of the binding sequence
        new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
      }
      if(MatchingUtils::matchReversedArgs(baseLit, alit)) {
        ArrayStoringBinder binder(altBindingData, variablePositions);
        MatchingUtils::matchTerms(*baseLit->nthArgument(0),*alit->nthArgument(1),binder);
        MatchingUtils::matchTerms(*baseLit->nthArgument(1),*alit->nthArgument(0),binder);

        *altBindingPtrs=altBindingData;
        altBindingPtrs++;
        altBindingData+=numVars;
        // add index of the literal in instance clause at the end of the binding sequence
        new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
      }
    } else {
      if(numVars) {
        ArrayStoringBinder binder(altBindingData, variablePositions);
        ALWAYS(MatchingUtils::matchArgs(baseLit,alit,binder));
      }

      *altBindingPtrs=altBindingData;
      altBindingPtrs++;
      altBindingData+=numVars;
      // add index of the literal in instance clause at the end of the binding sequence
      new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
    }
  }
  return true;
}

struct MatchingData {
  /**
   * The number of base literals.
   */
  unsigned len;

  /**
   * The number of variables for each base literal.
   *
   * varCnts[bi] is the number of variables in bases[bi].
   * 0 <= bi < len.
   */
  unsigned* varCnts;

  /**
   * For each base literal, an unsigned[] containing its variables in ascending order
   * (corresponding to the binding order in altBindings).
   *
   * boundVarNums[bi][i] is the i-th variable in bases[bi],
   * for 0 <= bi < len, 0 <= i < varCnts[bi].
   */
  unsigned** boundVarNums;

  /**
   * TermList[] corresponding to an alternative contains binding
   * for each variable of the base literal, and then one element
   * identifying the alternative literal itself.
   *
   * altBindings[bi][ai][i] is the term bound to the i-th variable of base literal bases[bi] when matched to its ai-th alternative,
   * for 0 <= bi < len, 0 <= ai < ???, 0 <= i < varCnts[bi].
   *
   * altBindings[bi][ai][varCnts[bi]].content() is the index of the ai-th alternative in instance,
   * for 0 <= bi < len, 0 <= ai < ???.
   */
  TermList*** altBindings;

  /**
   * The number of remaining alternatives for a base literal.
   *
   * In particular:
   * - remaining[b,0] is the number of possible alternatives for base literals bases[b].
   * - remaining[b,k] is the number of remaining alternatives for base literals bases[b] after binding bases[j] for 0 <= j < k to their currently selected alternatives.
   *                    (remaining means here that it is compatible to all variable bindings arising from the bindings for bases[j], 0 <= j < k)
   *
   * Below is an attempt to understand how it is computed (and why it is computed correctly).
   *
   * A triangular array, uninitialized at the start:
   *    ?
   *    ? ?
   *    ? ? ?
   *    ? ? ? ?
   *    ? ? ? ? ?
   *    ? ? ? ? ? ?
   *
   * Legend:
   *    ? uninitialized
   *    . initialized to some value
   *
   * ensureInit(bIndex)
   *    initializes the line bIndex
   *    (writes X from left to right)
   *    .
   *    . .
   *    X X X         <- line bIndex
   *    ? ? ? ?
   *    ? ? ? ? ?
   *    ? ? ? ? ? ?
   *
   * bindAlt(bIndex, altIndex)
   *    updates the column bIndex+1 (for all already initialized lines)
   *    (reads X and writes to the Y on its right; from top to bottom)
   *    .
   *    . .
   *    . . .
   *    . . X Y
   *    . . X Y .
   *    ? ? ? ? ? ?
   *        ^
   *      bIndex
   *
   * The backtracking algorithm at decision level bi (i.e., currently selecting an alternative for bases[bi])
   * uses remaining[bi,bi] as the number of alternatives that have to be checked at the current step.
   *
   * From above we see that the leftmost column is only written by ensureInit and always contains the total number of alternatives.
   * bindAlt prepares the next column for the next (and later) decision level.
   * ensureInit needs to refer to the current match data because the lines are only initialized on demand.
   * So if we only need e.g. two base literals to conclude that no match is possible, we never initialize lines 3+. This also saves update work in bindAlt for the early iterations.
   */
  TriangularArray<unsigned>* remaining;

  /**
   * nextAlts[bi] is the index of the next alternative to be selected at decision level bi,
   * for 0 <= bi < len.
   */
  unsigned* nextAlts;

  /**
   * eqLitForDemodulation is the index of the base literal selected for demodulation, or 0xFFFFFFFF if none has been selected.
   *
   * When eqLitForDemodulation is different from 0xFFFFFFFF, then bases[eqLitForDemodulation] is always a positive equality.
   */
  unsigned eqLitForDemodulation;

  /**
   * Stores the variables that are common to any two base literals.
   * See function 'getIntersectInfo'.
   */
  TriangularArray<pair<int,int>* >* intersections;

  /**
   * Base literals that are instantiated and matched to alternatives.
   *
   * bases[bi] is the bi-th base literal, with 0 <= bi < len.
   */
  Literal** bases;

  /**
   * bases[bi] can be matched to the alternatives in the list alts[bi], for 0 <= bi < len.
   * Each alternative must be part of the clause 'instance'.
   */
  LiteralList** alts;

  /**
   * The instance clause.
   * All literals in 'alts' must appear in this clause.
   */
  Clause* instance;

  // These are helper variables that just exist to allow us to use one large linear buffer
  // as underlying storage for all the other small arrays defined above.
  unsigned* boundVarNumStorage;
  TermList** altBindingPtrStorage;
  TermList* altBindingStorage;
  pair<int,int>* intersectionStorage;

  enum InitResult {
    OK,
    MUST_BACKTRACK,
    NO_ALTERNATIVE
  };

  unsigned getRemainingInCurrent(unsigned bi) const
  {
    return remaining->get(bi,bi);
  }

  unsigned getAltRecordIndex(unsigned bi, unsigned alti) const
  {
    return static_cast<unsigned>(altBindings[bi][alti][varCnts[bi]].content());
  }

  /**
   * Return true if binding @b b1Index -th base literal that binds variables
   * to terms stored in @b i1Bindings is compatible to binding @b b2Index -th
   * base literal that binds variables to terms stored in
   * @b altBindings[b2Index][i2AltIndex] .
   */
  bool compatible(unsigned b1Index, TermList* i1Bindings,
                  unsigned b2Index, unsigned i2AltIndex, pair<int,int>* iinfo)  // const
  {
    CALL("MatchingData::compatible");
    ASS_EQ(iinfo, getIntersectInfo(b1Index, b2Index));  // why is 'iinfo' passed at all? probably to save one call to getIntersectInfo. TODO: I don't think this makes much of a difference, so just the remove parameter 'iinfo'.

    TermList* i2Bindings=altBindings[b2Index][i2AltIndex];

    // Iterate over variables common to bases[b1Index] and bases[b2Index].
    // (iinfo stores which variables are in common and should be getIntersectInfo(b1Index, b2Index)).
    while(iinfo->first!=-1) {
      if(i1Bindings[iinfo->first]!=i2Bindings[iinfo->second]) {
        return false;
      }
      iinfo++;
    }
    return true;
  }

  /**
   * Bind base literal bases[bIndex] to alternative at altBindings[bIndex][altIndex].
   *
   * This function excludes alternatives for later base literals (i.e., bases[i] with i > bIndex)
   * that are not compatible with the current variable bindings.
   * Returns true iff all later base literals have at least one possible alternative left.
   *
   * (actually: not "all" later base literals, only all that have been initialized so far)
   */
  bool bindAlt(unsigned bIndex, unsigned altIndex)
  {
    CALL("MatchingData::bindAlt");

    // std::cerr << "bindAlt:   bIndex = " << bIndex << "\t" << bases[bIndex]->toString() << std::endl;
    // std::cerr << "         altIndex = " << altIndex << "\t" << (*instance)[getAltRecordIndex(bIndex, altIndex)]->toString() << std::endl;

    TermList* curBindings=altBindings[bIndex][altIndex];
    for(unsigned i=bIndex+1; i<len; i++) {
      // std::cerr << "\t i = " << i << "\t" << bases[i]->toString() << std::endl;
      if(!isInitialized(i)) {
        // std::cerr << "\t (not initialized)" << std::endl;
        // data not yet initialized for remaining base literals -> nothing to check (why?)
        for (unsigned j = i; j < len; ++j) { ASS(!isInitialized(j)); }
        break;
      }
      pair<int,int>* iinfo=getIntersectInfo(bIndex, i);
      unsigned remAlts=remaining->get(i,bIndex);
      // std::cerr << "\t remaining[" << i << ", " << bIndex << "] == " << remAlts << std::endl;

      if(iinfo->first!=-1) {  // checks whether we have any common variables at all
        // There are some variables in common
        for(unsigned ai=0;ai<remAlts;ai++) {
          if(!compatible(bIndex,curBindings,i,ai,iinfo)) {
            // If bindings are not compatible with alternative ai, move it to the back and decrease remaining number of alts by one,
            // effectively excluding it from being chosen in later steps.
            remAlts--;
            std::swap(altBindings[i][ai], altBindings[i][remAlts]);
            ai--;
          }
        }
      }
      if(remAlts==0) {
        // std::cerr << "\t bindAlts -> false" << std::endl;
        return false;
      }
      remaining->set(i,bIndex+1,remAlts);
      // std::cerr << "\t remaining[" << i << ", " << (bIndex+1) << "] := " << remAlts << std::endl;
    }
    // std::cerr << "\t bindAlts -> true" << std::endl;
    return true;
  }

  /**
   * Compute the "intersect info" of base literals bases[b1] and bases[b2], i.e.,
   * the variables that the literals have in common.
   * In particular, the result is an array of pair<int,int>.
   * Each element represents a variable that is common in bases[b1] and bases[b2];
   * the first and second components of the pair give the index i of the variable
   * in the array altBindings[bi][ai][i] for bi=b1 and bi=b2, respectively.
   * The returned array is terminated by a sentinel value that contains -1 in the first component.
   *
   * Requires b1 < b2.
   */
  pair<int,int>* getIntersectInfo(unsigned b1, unsigned b2)
  {
    CALL("MatchingData::getIntersectInfo");
    ASS(isInitialized(b1));
    ASS(isInitialized(b2));

    ASS_L(b1, b2);
    pair<int,int>* res=intersections->get(b2,b1);
    if( res ) {
      return res;
    }
    intersections->set(b2,b1, intersectionStorage);
    res=intersectionStorage;

    unsigned b1vcnt=varCnts[b1];
    unsigned b2vcnt=varCnts[b2];
    unsigned* b1vn=boundVarNums[b1];
    unsigned* b1vnStop=boundVarNums[b1]+b1vcnt;
    unsigned* b2vn=boundVarNums[b2];
    unsigned* b2vnStop=boundVarNums[b2]+b2vcnt;

    int b1VarIndex=0;
    int b2VarIndex=0;
    while(true) {
      while(b1vn!=b1vnStop && *b1vn<*b2vn) { b1vn++; b1VarIndex++; }
      if(b1vn==b1vnStop) { break; }
      while(b2vn!=b2vnStop && *b1vn>*b2vn) { b2vn++; b2VarIndex++; }
      if(b2vn==b2vnStop) { break; }
      if(*b1vn==*b2vn) {
        intersectionStorage->first=b1VarIndex;
        intersectionStorage->second=b2VarIndex;
        intersectionStorage++;

        b1vn++; b1VarIndex++;
        b2vn++; b2VarIndex++;
        if(b1vn==b1vnStop || b2vn==b2vnStop) { break; }
      }
    }

    intersectionStorage->first=-1;
    intersectionStorage++;

    return res;
  }

  bool isInitialized(unsigned bIndex) const {
    return boundVarNums[bIndex];
  }

  InitResult ensureInit(unsigned bIndex)
  {
    CALL("MatchingData::ensureInit");

    if(!isInitialized(bIndex)) {
      // std::cerr << "initialize: bIndex = " << bIndex << "\t" << bases[bIndex]->toString() << std::endl;
      boundVarNums[bIndex] = boundVarNumStorage;
      altBindings[bIndex] = altBindingPtrStorage;
      ALWAYS(createLiteralBindings(bases[bIndex], alts[bIndex], instance, boundVarNumStorage, altBindingPtrStorage, altBindingStorage));
      varCnts[bIndex] = boundVarNumStorage - boundVarNums[bIndex];

      unsigned altCnt=altBindingPtrStorage-altBindings[bIndex];
      if(altCnt==0) {
        // There is no matching alternative at all
        if (bases[bIndex]->isEquality() && bases[bIndex]->isPositive()) {
          // but for positive equalities, we may be able to select it for demodulation
          for(unsigned i = 0; i <= bIndex; i++) {
            remaining->set(bIndex, i, 0);  // TODO check if necessary (and correct...); we need at least remaining->set(bIndex,bIndex,0);
          }
          if (eqLitForDemodulation < bIndex) {
            // if a previous equality has already been selected (eqForDemodulation < bIndex), we can't select the current one.
            return MUST_BACKTRACK;
          } else {
            return OK;
          }
        } else {
          return NO_ALTERNATIVE;
        }
      }
      remaining->set(bIndex, 0, altCnt);
      // std::cerr << "\t remaining[" << bIndex << ", 0] := " << altCnt << std::endl;

      unsigned remAlts=0;
      for(unsigned pbi=0;pbi<bIndex;pbi++) { //pbi ~ previous base index
        pair<int,int>* iinfo=getIntersectInfo(pbi, bIndex);
        remAlts=remaining->get(bIndex, pbi);
        // std::cerr << "\t remaining[" << bIndex << ", " << pbi << "] == " << remAlts << std::endl;

        // TODO: convince myself that this changed condition (adding pbi != eqLitForDemodulation) is correct.
        // Problem: what does this part even do?
        // It somehow initializes the number of remaining alternatives.
        // We only do this for each bIndex once (since boundVarNums isn't set anywhere but in this function);
        // but it depends on the current matching state of the previous base literals??? (nextAlts[pbi])
        // How is that even correct...
        // TODO check again the interaction with bindAlt; I think we need to copy the column without change when selecting a baseLit for demodulation!
        if (pbi != eqLitForDemodulation && iinfo->first != -1) {
          TermList* pbBindings=altBindings[pbi][nextAlts[pbi]-1];
          for(unsigned ai=0;ai<remAlts;ai++) {
            if(!compatible(pbi, pbBindings, bIndex, ai, iinfo)) {
              remAlts--;
              std::swap(altBindings[bIndex][ai], altBindings[bIndex][remAlts]);
              ai--;
            }
          }
        }
        remaining->set(bIndex,pbi+1,remAlts);
        // std::cerr << "\t remaining[" << bIndex << ", " << (pbi+1) << "] := " << remAlts << std::endl;
      }
      if(bIndex>0 && remAlts==0) {
        return MUST_BACKTRACK;
      }
    }
    return OK;
  }

};

}  // namespace





namespace Kernel
{

using namespace Lib;


class MLMatcher2::Impl final
{
  public:
    CLASS_NAME(MLMatcher2::Impl);
    USE_ALLOCATOR(MLMatcher2::Impl);

    Impl();
    ~Impl() = default;

    void init(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts);
    bool nextMatch();

    Literal* getEqualityForDemodulation() const;

    void getMatchedAltsBitmap(v_vector<bool>& outMatchedBitmap) const;

    void getBindings(v_unordered_map<unsigned, TermList>& outBindings) const;

    // Disallow copy and move because the internal implementation still uses pointers to the underlying storage and it seems hard to untangle that.
    Impl(Impl const&) = delete;
    Impl(Impl&&) = delete;
    Impl& operator=(Impl const&) = delete;
    Impl& operator=(Impl&&) = delete;

  private:
    void initMatchingData(Literal** baseLits0, unsigned baseLen, Clause* instance, LiteralList** alts);

  private:
    // Backing storage for the pointers in s_matchingData, used and set up in initMatchingData
    DArray<Literal*> s_baseLits;
    DArray<LiteralList*> s_altsArr;
    DArray<unsigned> s_varCnts;
    DArray<unsigned*> s_boundVarNums;
    DArray<TermList**> s_altPtrs;
    TriangularArray<unsigned> s_remaining;
    TriangularArray<pair<int,int>* > s_intersections;
    DArray<unsigned> s_nextAlts;
    DArray<unsigned> s_boundVarNumData;
    DArray<TermList*> s_altBindingPtrs;
    DArray<TermList> s_altBindingsData;
    DArray<pair<int,int> > s_intersectionData;

    MatchingData s_matchingData;

    // For backtracking support
    DArray<unsigned> s_matchRecord;
    unsigned s_currBLit;
    int s_counter;
};


MLMatcher2::Impl::Impl()
  : s_baseLits(32)
  , s_altsArr(32)
  , s_varCnts(32)
  , s_boundVarNums(32)
  , s_altPtrs(32)
  , s_remaining(32)
  , s_intersections(32)
  , s_nextAlts(32)
  , s_boundVarNumData(64)
  , s_altBindingPtrs(128)
  , s_altBindingsData(256)
  , s_intersectionData(128)
  , s_matchRecord(32)
{ }


void MLMatcher2::Impl::initMatchingData(Literal** baseLits0, unsigned baseLen, Clause* instance, LiteralList** alts)
{
  CALL("MLMatcher2::Impl::initMatchingData");

  s_baseLits.initFromArray(baseLen,baseLits0);
  s_altsArr.initFromArray(baseLen,alts);

  s_varCnts.ensure(baseLen);
  s_boundVarNums.init(baseLen,0);
  s_altPtrs.ensure(baseLen);
  s_remaining.setSide(baseLen);
  s_nextAlts.ensure(baseLen);

  s_intersections.setSide(baseLen);
  s_intersections.zeroAll();

  //number of base literals that have zero alternatives
  unsigned zeroAlts=0;
  //number of base literals that have at most one alternative
  unsigned singleAlts=0;
  size_t baseLitVars=0;
  size_t altCnt=0;
  size_t altBindingsCnt=0;

  unsigned mostDistVarsLit=0;
  unsigned mostDistVarsCnt=s_baseLits[0]->getDistinctVars();

  // Helper function to swap base literals at indices i and j
  auto swapLits = [this] (int i, int j) {
    std::swap(s_baseLits[i], s_baseLits[j]);
    std::swap(s_altsArr[i], s_altsArr[j]);
  };

  // Reorder base literals to try and reduce backtracking
  // Order:
  // 1. base literals with zero alternatives
  // 2. base literals with one alternative
  // 3. from the remaining base literals the one with the most distinct variables
  // 4. the rest
  for(unsigned i=0;i<baseLen;i++) {
    unsigned distVars=s_baseLits[i]->getDistinctVars();

    baseLitVars+=distVars;
    unsigned currAltCnt=0;
    LiteralList::Iterator ait(s_altsArr[i]);
    while(ait.hasNext()) {
      currAltCnt++;
      if(ait.next()->commutative()) {
        currAltCnt++;
      }
    }

    altCnt += currAltCnt;
    altBindingsCnt += (distVars+1)*currAltCnt;

    ASS_LE(zeroAlts, singleAlts);
    ASS_LE(singleAlts, i);
    if(currAltCnt==0) {
      if(zeroAlts!=i) {
        if(singleAlts!=zeroAlts) {
          swapLits(singleAlts, zeroAlts);
        }
        swapLits(i, zeroAlts);
        if(mostDistVarsLit==singleAlts) {
          mostDistVarsLit=i;
        }
      }
      zeroAlts++;
      singleAlts++;
    } else if (currAltCnt==1) {
      if(singleAlts!=i) {
        swapLits(i, singleAlts);
        if(mostDistVarsLit==singleAlts) {
          mostDistVarsLit=i;
        }
      }
      singleAlts++;
    } else if(i>0 && mostDistVarsCnt<distVars) {
      mostDistVarsLit=i;
      mostDistVarsCnt=distVars;
    }
  }
  if(mostDistVarsLit>singleAlts) {
    swapLits(mostDistVarsLit, singleAlts);
  }

  s_boundVarNumData.ensure(baseLitVars);
  s_altBindingPtrs.ensure(altCnt);
  s_altBindingsData.ensure(altBindingsCnt);
  s_intersectionData.ensure((baseLitVars+baseLen)*baseLen);

  s_matchingData.len=baseLen;
  s_matchingData.varCnts=s_varCnts.array();
  s_matchingData.boundVarNums=s_boundVarNums.array();
  s_matchingData.altBindings=s_altPtrs.array();
  s_matchingData.remaining=&s_remaining;
  s_matchingData.nextAlts=s_nextAlts.array();
  s_matchingData.intersections=&s_intersections;

  s_matchingData.bases=s_baseLits.array();
  s_matchingData.alts=s_altsArr.array();
  s_matchingData.instance=instance;
  s_matchingData.eqLitForDemodulation = 0xFFFFFFFF;

  s_matchingData.boundVarNumStorage=s_boundVarNumData.array();
  s_matchingData.altBindingPtrStorage=s_altBindingPtrs.array();
  s_matchingData.altBindingStorage=s_altBindingsData.array();
  s_matchingData.intersectionStorage=s_intersectionData.array();
}


void MLMatcher2::Impl::init(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts)
{
  CALL("MLMatcher2::Impl::init");

  initMatchingData(baseLits, baseLen, instance, alts);

  unsigned const matchRecordLen = instance->length();
  s_matchRecord.init(matchRecordLen, 0xFFFFFFFF);
  // What is the matchRecord?
  //   Index is retrieved by getAltRecordIndex:  md->getAltRecordIndex(currBLit, md->nextAlts[currBLit])
  //   The index is the position of the alt literal in 'instance'
  //   Value is compared to currBLit, so it should refer to a base literal
  //
  // So from currBLit we get a record index, and the record is a base literal again???
  //
  // Hypothesis:
  //   The match record tracks for each literal of the instance which base literal is matched to it.
  //   This means it is only necessary for multiset matching (because each instance literal can only be used once for matching).
  ASS_EQ(s_matchRecord.size(), matchRecordLen);

  s_matchingData.nextAlts[0] = 0;
  s_currBLit = 0;
  s_counter = 0;
}


bool MLMatcher2::Impl::nextMatch()
{
  CALL("MLMatcher2::Impl::nextMatch");
  MatchingData* const md = &s_matchingData;

  // TODO clarify
  while (true) {
    MatchingData::InitResult ires = md->ensureInit(s_currBLit);
    if (ires != MatchingData::OK) {
      if (ires == MatchingData::MUST_BACKTRACK) {
        s_currBLit--;
        continue;
      } else {
        ASS_EQ(ires, MatchingData::NO_ALTERNATIVE);
        return false;
      }
    }

    // TODO for FSD:
    // if this is the last positive equality and none have been selected for demodulation yet,
    // then select this one and skip all other choices.
    // supporting this, also in initMatchingData move equalities to the top (within the now existing groups?)
    // (if we want to merge subsumption into FSD, we probably should not do this)
    //
    // Idea:
    // class MatchProblem
    // which stores base, alts etc. (one instance of the matching problem)
    // - also has flag: checkSubsumption
    //   if checkSubsumption is off, then force one equality to be selected in all branches (as in comment above)
    // - (we might not need the flag though... when would we set this to false? if there is an equality without alts, i.e. subsumption is impossible a priori.
    //    but even in this case, we will order this literal first and thus select the equality anyways; there is no other choice for this literal.)
    // - why a class to store MatchProblem?
    //   It can play a role analogous to the ClauseMatches in ForwardSubsumptionAndResolution.
    //   The idea there is to keep the MatchProblem to re-use it after subsumption to check subsumption resolution as well.

    unsigned maxAlt = md->getRemainingInCurrent(s_currBLit);
    while (md->nextAlts[s_currBLit] < maxAlt &&
           (
             // Reject the current alternative (i.e., nextAlts[currBLit]) if
             // 1. The alt is already matched to a base literal (recall that we are doing multiset matching), or
             s_matchRecord[md->getAltRecordIndex(s_currBLit, md->nextAlts[s_currBLit])] < s_currBLit 
             // 2. The current variable bindings are not compatible with the alternative
             || !md->bindAlt(s_currBLit, md->nextAlts[s_currBLit])
           )
          ) {
      md->nextAlts[s_currBLit]++;
    }

    if (md->nextAlts[s_currBLit] < maxAlt) {
      // Got a suitable alternative in nextAlt
      // bases[s_currBLit] is matched to alternative instance[matchRecordIndex]

      // Unassign existing match records for this level
      for (unsigned i = 0; i < s_matchRecord.size(); i++) {
        if (s_matchRecord[i] == s_currBLit) {
          s_matchRecord[i] = 0xFFFFFFFF;
        }
      }
      // Set new match record (match record content is the base index for each instance index)
      unsigned matchRecordIndex = md->getAltRecordIndex(s_currBLit, md->nextAlts[s_currBLit]);
      ASS_G(s_matchRecord[matchRecordIndex], s_currBLit);  // new match record cannot be set already
      s_matchRecord[matchRecordIndex] = s_currBLit;

      md->nextAlts[s_currBLit]++;
      s_currBLit++;  // go to next level
      if (s_currBLit == md->len) { break; }  // full match
      md->nextAlts[s_currBLit] = 0;
      if (md->eqLitForDemodulation == s_currBLit) { md->eqLitForDemodulation = 0xFFFFFFFF; }
    } else {
      // No alt left for currBLit
      ASS_GE(md->nextAlts[s_currBLit], maxAlt);

      if (md->bases[s_currBLit]->isEquality() && md->bases[s_currBLit]->isPositive() && md->eqLitForDemodulation > s_currBLit) {
        // Select current base literal as equality for demodulation
        md->eqLitForDemodulation = s_currBLit;
        s_currBLit++;  // go to next level
        if (s_currBLit == md->len) { break; }  // full match
        md->nextAlts[s_currBLit] = 0;
      } else {
        // Backtrack
        if (s_currBLit == 0) { return false; }
        s_currBLit--;
      }
    }

    s_counter++;
    if(s_counter==50000) {
      // std::cerr << "counter reached 50k" << std::endl;
      s_counter=0;
      if(env.timeLimitReached()) {
        throw TimeLimitExceededException();
      }
    }

  } // while (true)

  s_currBLit--;  // prepare for next round
  return true;
}

Literal* MLMatcher2::Impl::getEqualityForDemodulation() const
{
  MatchingData const* const md = &s_matchingData;

  if (md->eqLitForDemodulation > md->len) {
    ASS_EQ(md->eqLitForDemodulation, 0xFFFFFFFF);
    return nullptr;
  } else {
    return md->bases[md->eqLitForDemodulation];
  }
}

void MLMatcher2::Impl::getMatchedAltsBitmap(v_vector<bool>& outMatchedBitmap) const
{
  MatchingData const* const md = &s_matchingData;

  outMatchedBitmap.clear();
  outMatchedBitmap.resize(md->instance->length(), false);

  for (unsigned bi = 0; bi < md->len; ++bi) {
    if (bi != md->eqLitForDemodulation) {
      unsigned alti = md->nextAlts[bi] - 1;
      unsigned i = md->getAltRecordIndex(bi, alti);
      outMatchedBitmap[i] = true;
    }
  }
  // outMatchedBitmap[i] == true iff instance[i] is matched by some literal of base
}


void MLMatcher2::Impl::getBindings(v_unordered_map<unsigned, TermList>& outBindings) const
{
  MatchingData const* const md = &s_matchingData;

  ASS(outBindings.empty());

  for (unsigned bi = 0; bi < md->len; ++bi) {
    if (bi != md->eqLitForDemodulation) {
      Literal* b = md->bases[bi];
      unsigned alti = md->nextAlts[bi] - 1;
      for (unsigned vi = 0; vi < md->varCnts[bi]; ++vi) {
        // md->altBindings[bi][alti] contains bindings for the variables in b, ordered by the variable index.
        // md->boundVarNums[bi] contains the corresponding variable indices.
        unsigned var = md->boundVarNums[bi][vi];
        TermList trm = md->altBindings[bi][alti][vi];
        auto res = outBindings.insert({var, trm});
        auto it = res.first;
        bool inserted = res.second;
        if (!inserted) {
          ASS_EQ(it->second, trm);
        }
      }
    }
  }
}


MLMatcher2::MLMatcher2()
  : m_impl{nullptr}
{ }

void MLMatcher2::init(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts)
{
  if (!m_impl) {
    m_impl = make_unique<MLMatcher2::Impl>();
  }
  m_impl->init(baseLits, baseLen, instance, alts);
}

MLMatcher2::~MLMatcher2() = default;

bool MLMatcher2::nextMatch()
{
  ASS(m_impl);
  return m_impl->nextMatch();
}

Literal* MLMatcher2::getEqualityForDemodulation() const
{
  ASS(m_impl);
  return m_impl->getEqualityForDemodulation();
}

void MLMatcher2::getMatchedAltsBitmap(v_vector<bool>& outMatchedBitmap) const
{
  ASS(m_impl);
  m_impl->getMatchedAltsBitmap(outMatchedBitmap);
}

void MLMatcher2::getBindings(v_unordered_map<unsigned, TermList>& outBindings) const
{
  ASS(m_impl);
  m_impl->getBindings(outBindings);
}


}  // namespace Kernel
