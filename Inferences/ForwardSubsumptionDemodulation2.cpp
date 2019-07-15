#include "ForwardSubsumptionDemodulation2.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MLMatcher2.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Lib/ScopeGuard.hpp"
#include "Lib/STL.hpp"
#include "Lib/STLAllocator.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/TPTPPrinter.hpp"
#include <array>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace Kernel;
using namespace Lib;
using namespace Inferences;
using namespace Saturation;


// Set to true to output FSD inferences on stdout
#define FSD_LOG_INFERENCES false


void ForwardSubsumptionDemodulation2::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardSubsumptionDemodulation2::attach");
  ForwardSimplificationEngine::attach(salg);

  auto index_type = getOptions().forwardSubsumptionDemodulationUseSeparateIndex() ? FSD_SUBST_TREE : FW_SUBSUMPTION_SUBST_TREE;
  _index.request(salg->getIndexManager(), index_type);

  _preorderedOnly = false;
  _allowIncompleteness = false;
  _doSubsumption = getOptions().forwardSubsumptionDemodulationIncludeSubsumption();

  if (_doSubsumption) {
    _unitIndex.request(salg->getIndexManager(), SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  }



  // // Small test case for MLMatcher2
  // unsigned p = env.signature->addPredicate("p", 1);
  // unsigned q = env.signature->addPredicate("q", 1);
  // unsigned r = env.signature->addPredicate("r", 2);
  // unsigned s = env.signature->addPredicate("s", 1);
  // unsigned fn_c = env.signature->addFunction("c", 0);
  // unsigned fn_d = env.signature->addFunction("d", 0);
  // unsigned fn_e = env.signature->addFunction("e", 0);
  // unsigned fn_f = env.signature->addFunction("f", 0);

  // TermList x = TermList(0, false);
  // TermList y = TermList(1, false);
  // TermList c = TermList(Term::create(fn_c, 0, nullptr));
  // TermList d = TermList(Term::create(fn_d, 0, nullptr));
  // TermList e = TermList(Term::create(fn_e, 0, nullptr));
  // TermList f = TermList(Term::create(fn_f, 0, nullptr));

  // Literal* rxy = Literal::create2(r, true, x, y);
  // Literal* rdd = Literal::create2(r, true, d, d);
  // Literal* rcd = Literal::create2(r, true, c, d);
  // Literal* rcc = Literal::create2(r, true, c, c);

  // Literal* px = Literal::create1(p, true, x);
  // Literal* pc = Literal::create1(p, true, c);
  // Literal* pd = Literal::create1(p, true, d);

  // Literal* qx = Literal::create1(q, true, x);
  // Literal* qd = Literal::create1(q, true, d);
  // Literal* qe = Literal::create1(q, true, e);
  // Literal* qf = Literal::create1(q, true, f);

  // Literal* sy = Literal::create1(s, true, y);
  // Literal* sd = Literal::create1(s, true, d);
  // Literal* sc = Literal::create1(s, true, c);

  // LiteralList* alts0 = LiteralList::empty();
  // LiteralList::push(rdd, alts0);
  // LiteralList::push(rcd, alts0);
  // LiteralList::push(rcc, alts0);

  // LiteralList* alts1 = LiteralList::empty();
  // LiteralList::push(pd, alts1);
  // LiteralList::push(pc, alts1);

  // LiteralList* alts2 = LiteralList::empty();
  // LiteralList::push(qe, alts2);
  // LiteralList::push(qd, alts2);
  // LiteralList::push(qf, alts2);

  // LiteralList* alts3 = LiteralList::empty();
  // LiteralList::push(sd, alts3);
  // LiteralList::push(sc, alts3);

  // Literal* bases[] = {rxy, px, qx, sy};
  // LiteralList* alts[] = {alts0, alts1, alts2, alts3};

  // LiteralStack lits;
  // lits.push(rdd);
  // lits.push(rcd);
  // lits.push(rcc);
  // lits.push(pc);
  // lits.push(pd);
  // lits.push(qe);
  // lits.push(qd);
  // lits.push(qf);
  // lits.push(sd);
  // lits.push(sc);
  // Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));

  // MLMatcher2 matcher;
  // matcher.init(bases, 4, cl, alts);

  // bool res = matcher.nextMatch();
  // std::cerr << "match? " << res << std::endl;
  // std::exit(27);


  // // Small test case for MLMatcher2 (b)
  // // .
  // // bases[0] = ~end_point(X3,X0)
  // // bases[1] = X1 = X3
  // // bases[2] = X1 = X2
  // // bases[3] = X2 = X3
  // // bases[4] = ~end_point(X2,X0)
  // // bases[5] = ~end_point(X1,X0)
  // // instance = sK5(X1) = X0 | X0 = X2 | sK5(X1) = X2 | ~end_point(X2,X1) | ~end_point(X0,X1) | closed(X1)
  // // .
  // // Leads to:
  // // Condition remAlts > 0 in file ../Kernel/MLMatcher2.cpp, line 508 was violated, as:
  // // remAlts == 0
  // // 0 == 0
  // unsigned p = env.signature->addPredicate("p", 2);
  // unsigned q = env.signature->addPredicate("q", 1);
  // unsigned f = env.signature->addFunction("f", 1);

  // TermList x0 = TermList(0, false);
  // TermList x1 = TermList(1, false);
  // TermList x2 = TermList(2, false);
  // TermList x3 = TermList(3, false);
  // TermList fx1 = TermList(Term::create1(f, x1));

  // Literal* b0 = Literal::create2(p, false, x3, x0);
  // Literal* b1 = Literal::createEquality(true, x1, x3, 0);
  // Literal* b2 = Literal::createEquality(true, x1, x2, 0);
  // Literal* b3 = Literal::createEquality(true, x2, x3, 0);
  // Literal* b4 = Literal::create2(p, false, x2, x0);
  // Literal* b5 = Literal::create2(p, false, x1, x0);

  // Literal* i0 = Literal::createEquality(true, fx1, x0, 0);
  // Literal* i1 = Literal::createEquality(true, x0, x2, 0);
  // Literal* i2 = Literal::createEquality(true, fx1, x2, 0);
  // Literal* i3 = Literal::create2(p, false, x2, x1);
  // Literal* i4 = Literal::create2(p, false, x0, x1);
  // Literal* i5 = Literal::create1(q, false, x1);

  // LiteralList* alts0 = LiteralList::empty();
  // LiteralList::push(i3, alts0);
  // LiteralList::push(i4, alts0);

  // LiteralList* alts1 = LiteralList::empty();
  // LiteralList::push(i0, alts1);
  // LiteralList::push(i1, alts1);
  // LiteralList::push(i2, alts1);

  // LiteralList* alts2 = alts1;
  // LiteralList* alts3 = alts1;

  // LiteralList* alts4 = alts0;
  // LiteralList* alts5 = alts0;

  // Literal* bases[] = {b0, b1, b2, b3, b4, b5};
  // LiteralList* alts[] = {alts0, alts1, alts2, alts3, alts4, alts5};

  // LiteralStack lits;
  // lits.push(i0);
  // lits.push(i1);
  // lits.push(i2);
  // lits.push(i3);
  // lits.push(i4);
  // lits.push(i5);
  // Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));

  // MLMatcher2 matcher;
  // matcher.init(bases, 6, cl, alts);
  // // MLMatcher matcher;
  // // // matcher.init(bases, 6, cl, alts, true);
  // // // matcher.init(bases, 6, cl, alts, false);

  // bool res = matcher.nextMatch();
  // std::cerr << "match? " << res << std::endl;
  // std::exit(27);


  // // Small test case for MLMatcher2 (c)
  // // Should find a match but doesn't due to too aggressive pruning.
  // unsigned p = env.signature->addPredicate("p", 2);
  // unsigned q = env.signature->addPredicate("q", 1);
  // unsigned f = env.signature->addFunction("f", 1);

  // TermList x0 = TermList(0, false);
  // TermList x1 = TermList(1, false);
  // TermList x2 = TermList(2, false);
  // TermList x3 = TermList(3, false);
  // TermList fx0 = TermList(Term::create1(f, x0));
  // TermList fx1 = TermList(Term::create1(f, x1));
  // TermList c = TermList(Term::createConstant("c"));
  // TermList d = TermList(Term::createConstant("d"));
  // TermList fc = TermList(Term::create1(f, c));
  // TermList fd = TermList(Term::create1(f, d));

  // Literal* b0 = Literal::create2(p, true, x0, fx0);
  // Literal* b1 = Literal::create2(p, true, x1, fx1);
  // Literal* b2 = Literal::createEquality(true, x0, x1, 0);

  // Literal* i0 = Literal::create2(p, true, c, fc);
  // Literal* i1 = Literal::create2(p, true, d, fd);
  // Literal* i2 = Literal::createEquality(true, c, fd, 0);

  // // LiteralList* alts0 = LiteralList::empty();
  // // LiteralList::push(i0, alts0);
  // // LiteralList::push(i1, alts0);
  // // LiteralList* alts1 = alts0;

  // LiteralList* alts0 = LiteralList::empty();
  // LiteralList::push(i0, alts0);
  // // LiteralList::push(i0, alts0);
  // LiteralList* alts1 = LiteralList::empty();
  // LiteralList::push(i1, alts1);
  // // LiteralList::push(i1, alts1);

  // LiteralList* alts2 = LiteralList::empty();
  // LiteralList::push(i2, alts2);
  // LiteralList::push(i2, alts2);

  // // Literal* bases[] = {b2, b1, b0};
  // // LiteralList* alts[] = {alts2, alts1, alts0};
  // Literal* bases[] = {b0, b1, b2};
  // LiteralList* alts[] = {alts0, alts1, alts2};

  // LiteralStack lits;
  // lits.push(i0);
  // lits.push(i1);
  // lits.push(i2);
  // Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));

  // MLMatcher2 matcher;
  // matcher.init(bases, 3, cl, alts);

  // bool res = matcher.nextMatch();
  // std::cerr << "match? " << res << std::endl;
  // std::exit(27);


  // TODO: Add the following test case
  //  bases[0]: sK6(sK15) = X6
  //       alt:      sK6(sK15) = sK10(sK13,X12)
  //       alt:      sK6(sK15) = X11
  //  bases[1]: sK6(sK15) = X5
  //       alt:      sK6(sK15) = sK10(sK13,X12)
  //       alt:      sK6(sK15) = X11
  //  bases[2]: X5 = X6
  //       alt:      sK6(sK15) = sK10(sK13,X12)
  //       alt:      sK10(sK13,X12) = X11
  //       alt:      sK6(sK15) = X11
  //  bases[3]: ~end_point(X6,sK13)
  //       alt:      ~end_point(X12,sK13)
  //       alt:      ~end_point(X11,sK13)
  //  bases[4]: ~end_point(X5,sK13)
  //       alt:      ~end_point(X12,sK13)
  //       alt:      ~end_point(X11,sK13)
  //  instance: 4301. sK6(sK15) = X11 | sK6(sK15) = sK10(sK13,X12) | sK10(sK13,X12) = X11 | ~end_point(X11,sK13) | ~end_point(X12,sK13) <- (24) [resolution 315,402]
}


void ForwardSubsumptionDemodulation2::detach()
{
  CALL("ForwardSubsumptionDemodulation2::detach");
  _index.release();
  ForwardSimplificationEngine::detach();
}


namespace {


/**
 * A binder that consists of two maps: a base and an overlay.
 * Lookup first checks the base map, then the overlay map.
 * New bindings are added to the overlay map.
 *
 * In FSD, the base bindings are extracted from the MLMatcher and correspond to the subsumption part,
 * while the overlay bindings are from the demodulation part (i.e., from
 * matching the lhs of the demodulation equality to the candidate term that
 * might be simplified).
 *
 * This class implements the Binder interface as described in Kernel/Matcher.hpp,
 * and the Applicator interface as described in Kernel/SubstHelper.hpp.
 */
class OverlayBinder
{
  public:
    using Var = unsigned int;
    using BindingsMap = v_unordered_map<Var, TermList>;

    OverlayBinder()
      : m_base(16)
      , m_overlay(16)
    { }

    /// Initializes the base bindings with the given argument
    explicit
    OverlayBinder(BindingsMap&& initialBindings)
      : m_base(std::move(initialBindings))
      , m_overlay(16)
    { }

    bool bind(Var var, TermList term)
    {
      // If the variable is already bound, it must be bound to the same term.
      auto base_it = m_base.find(var);
      if (base_it != m_base.end()) {
        return base_it->second == term;
      }
      else {
        auto res = m_overlay.insert({var, term});
        auto it = res.first;
        bool inserted = res.second;
        return inserted || (it->second == term);
      }
    }

    void specVar(Var var, TermList term)
    {
      ASSERTION_VIOLATION;
    }

    /// Clear all bindings
    void clear()
    {
      m_base.clear();
      m_overlay.clear();
    }

    /// Direct access to base bindings.
    /// The returned map may only be modified if the overlay map is empty!
    /// (this function is unfortunately necessary to be able to extract the base bindings from the MLMatcher without dynamic memory allocation)
    BindingsMap& base()
    {
      ASS(m_overlay.empty());
      return m_base;
    }

    /// Resets to base bindings
    void reset() {
      m_overlay.clear();
    }

    // Makes objects of this class work as applicator for substitution
    // (as defined in Kernel/SubstHelper.hpp)
    TermList apply(Var var) const {
      auto b_it = m_base.find(var);
      if (b_it != m_base.end()) {
        return b_it->second;
      } else {
        auto o_it = m_overlay.find(var);
        if (o_it != m_overlay.end()) {
          return o_it->second;
        } else {
          // If var is not bound, return the variable itself (as TermList)
          return TermList(var, false);
        }
      }
    }

    TermList applyTo(TermList t, bool noSharing = false) const {
      return SubstHelper::apply(t, *this, noSharing);
    }

    Literal* applyTo(Literal* l) const {
      return SubstHelper::apply(l, *this);
    }

  private:
    BindingsMap m_base;
    BindingsMap m_overlay;

    friend std::ostream& operator<<(std::ostream& o, OverlayBinder const& binder);
};  // class OverlayBinder

std::ostream& operator<<(std::ostream& o, OverlayBinder const& binder)
{
  o << "OverlayBinder { ";
  bool first = true;
  for (auto binding : binder.m_base) {
    if (!first) {
      o << ", ";
    } else {
      first = false;
    }
    o << TermList(binding.first, false).toString() << " -> " << binding.second.toString();
  }
  o << " / ";
  first = true;
  for (auto binding : binder.m_overlay) {
    if (!first) {
      o << ", ";
    } else {
      first = false;
    }
    o << TermList(binding.first, false).toString() << " -> " << binding.second.toString();
  }
  o << " }";
  return o;
}


}  // namespace


bool ForwardSubsumptionDemodulation2::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardSubsumptionDemodulation2::perform");

  //                        cl
  //                 vvvvvvvvvvvvvvvv
  //     mcl       matched      /-- only look for a term to demodulate in this part!
  // vvvvvvvvvv      vv    vvvvvvvvvv
  // eqLit                  dlit
  // vvvvv                 vvvvv
  //
  // l = r \/ C      CΘ \/ L[lΘ] \/ D
  // --------------------------------
  //       CΘ \/ L[rΘ] \/ D
  //
  // where
  // 1. lΘ > rΘ, and
  // 2. l = r \/ C  <  CΘ \/ L[lΘ] \/ D   (to ensure the right premise is redundant after the inference)
  //
  // For condition 2, we check that l = r < M for some M in L \/ D.

  TimeCounter tc(TC_FORWARD_SUBSUMPTION_DEMODULATION);

  Ordering& ordering = _salg->getOrdering();

  // Discard all previous aux values (so after this, hasAux() returns false for any clause).
  Clause::requestAux();
  ON_SCOPE_EXIT({ Clause::releaseAux(); });

  // Subsumption by unit clauses
  if (_doSubsumption) {
    for (unsigned sqli = 0; sqli < cl->length(); ++sqli) {
      SLQueryResultIterator rit = _unitIndex->getGeneralizations((*cl)[sqli], false, false);
      while (rit.hasNext()) {
        Clause* premise = rit.next().clause;

        if (premise->hasAux()) {
          continue;  // we've already checked this premise
        }
        premise->setAux(nullptr);

        if (!ColorHelper::compatible(cl->color(), premise->color())) {
          continue;
        }

        ASS(!getOptions().forwardSubsumption());  // if FS is enabled, it should have found this inference already before
        premises = pvi(getSingletonIterator(premise));
        env.statistics->forwardSubsumed++;
        return true;
      }
    }
  }

  // Initialize miniIndex with literals in the clause cl
  // TODO(idea for later): maybe it helps to order alternatives, either smaller to larger or larger to smaller, or unordered
  // to do this, we can simply order the literals inside the miniIndex (i.e., in each equivalence class w.r.t. literal header)
  LiteralMiniIndex miniIndex(cl);

  for (unsigned sqli = 0; sqli < cl->length(); ++sqli) {
    Literal* subsQueryLit = (*cl)[sqli];  // this literal is only used to query the subsumption index

    /**
     * Step 1: find candidate clauses for subsumption
     */
    SLQueryResultIterator rit = _index->getGeneralizations(subsQueryLit, false, false);
    while (rit.hasNext()) {
      SLQueryResult res = rit.next();
      Clause* mcl = res.clause;  // left premise of FSD

      ASS_NEQ(cl, mcl);  // this can't happen because cl isn't in the index yet

      // (this check exists only to improve performance and does not affect correctness)
      if (mcl->hasAux()) {
        // we've already checked this clause
        continue;
      }
      mcl->setAux(nullptr);

      // No multiset match possible if base is longer than instance
      // (this check exists only to improve performance and does not affect correctness)
      if (mcl->length() > cl->length()) {
        continue;
      }

      if (!ColorHelper::compatible(cl->color(), mcl->color())) {
        continue;
      }

      /**
       * Step 2: choose a positive equality in mcl to use for demodulation and try to instantiate the rest to some subset of cl
       */
      static v_vector<LiteralList*> alts;
      alts.clear();
      alts.reserve(mcl->length());
      ASS_EQ(alts.size(), 0);
      unsigned baseLitsWithoutAlternatives = 0;
      for (unsigned mi = 0; mi < mcl->length(); ++mi) {
        Literal* baseLit = (*mcl)[mi];

        LiteralMiniIndex::InstanceIterator instIt(miniIndex, baseLit, false);

        if (!instIt.hasNext()) {
          // baseLit does not have any suitable alternative at all!
          //
          // If there are base literals without any suitable alternatives:
          // 1. If there is only one literal without alternative and it is a positive equality,
          //    then it might still be possible to get an FSD inference by choosing this literal
          //    as equality for demodulation.
          // 2. If there is a literal without alternative but it is not a positive equality,
          //    then it is impossible to get an FSD inference.
          // 3. If there are two literals without alternatives, then it is impossible as well.
          //
          // (This check exists purely for performance reasons.
          // MLMatcher would exclude cases 2 and 3 as well, but with additional overhead.)
          //
          // Note that we do not have to check whether mcl contains a positive equality at all.
          // There are two useful configurations to consider:
          // a. We do not want to do forward subsumption here and are using the FSD index.
          //    The FSD index only contains clauses that have a positive equality, and mcl is chosen from this index.
          // b. We do forward subsumption as part of FSD and are using the (adjusted) FS index.
          //    In this case we do not want to exclude an mcl without positive equality anyways.
          baseLitsWithoutAlternatives += 1;
          if (baseLitsWithoutAlternatives == 1) {
            if (!baseLit->isEquality() || !baseLit->isPositive()) {
              // We are in case 2 => skip
              baseLitsWithoutAlternatives += 1;  // a hack so we don't need another variable to check whether to skip below (in other words, merge case 2 into case 3 for purpose of the "if" below)
              break;
            }
          } else {
            // We are in case 3 => skip
            ASS_G(baseLitsWithoutAlternatives, 1);
            break;
          }
        }

        LiteralList* l = nullptr;
        while (instIt.hasNext()) {
          Literal* matched = instIt.next();
          LiteralList::push(matched, l);
        }
        alts.push_back(l);
      }

      // Ensure cleanup of LiteralLists
      ON_SCOPE_EXIT({
        for (LiteralList* ll : alts) {
          LiteralList::destroy(ll);
        }
      });

      // Skip due to missing alternatives? (see comment above, "baseLit does not have any suitable alternative")
      if (baseLitsWithoutAlternatives > 1) {
        // static unsigned cnt = 0;
        // std::cerr << "skipped due to baseLitsWithoutAlternatives: " << ++cnt << std::endl;
        continue;
      }

      ASS_EQ(mcl->length(), alts.size());

      static MLMatcher2 matcher;
      matcher.init(mcl, cl, alts.data());

      static unsigned const maxMatches =
        getOptions().forwardSubsumptionDemodulationMaxMatches() == 0
        ? std::numeric_limits<decltype(maxMatches)>::max()
        : getOptions().forwardSubsumptionDemodulationMaxMatches();

      for (unsigned numMatches = 0; numMatches < maxMatches; ++numMatches) {
        if (!matcher.nextMatch()) {
          break;
        }

        Literal* eqLit = matcher.getEqualityForDemodulation();
        if (!eqLit) {
          // eqLit == nullptr means that the whole of mcl can be instantiated to some subset of cl,
          // i.e., cl is subsumed by mcl.
          //
          // Note that we should always apply Forward Subsumption if possible,
          // because it is a deletion rule; and Forward Subsumption should be performed before FSD.
          ASS(!getOptions().forwardSubsumption());  // if FS is enabled, it should have found this inference already before
          premises = pvi(getSingletonIterator(mcl));
          env.statistics->forwardSubsumed++;
          return true;
        }
        ASS(eqLit->isEquality());
        ASS(eqLit->isPositive());

        unsigned const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

        Ordering::Result const eqArgOrder = ordering.getEqualityArgumentOrder(eqLit);
        bool const preordered = (eqArgOrder == Ordering::LESS) || (eqArgOrder == Ordering::GREATER);
        if (_preorderedOnly && !preordered) {
          continue;
        }

        // isMatched[i] is true iff (*cl)[i] is matched my some literal in mcl (without eqLit)
        static v_vector<bool> isMatched;
        matcher.getMatchedAltsBitmap(isMatched);

        static OverlayBinder binder;
        binder.clear();
        matcher.getBindings(binder.base());

        /**
         * Step 3: now we try to demodulate some term in an unmatched literal with eqLit.
         *
         * IMPORTANT: only look at literals that are not being matched to mcl (the rule is unsound otherwise)!
         *
         *       mcl                cl
         *   vvvvvvvvvv      vvvvvvvvvvvvvvvv
         *   eqLit         matched      /-- only look for a term to demodulate in this part!
         *   vvvvv           vv    vvvvvvvvvv
         *   l = r \/ C      CΘ \/ L[lΘ] \/ D
         *   --------------------------------
         *         CΘ \/ L[rΘ] \/ D
         *
         */

        // Select candidate lhs of eqLit for demodulation.
        // Must be larger than the rhs after substitution.
        //
        // Three possible outcomes:
        // 1. No LHS (if INCOMPARABLE and different variables)
        // 2. One LHS
        // 3. Two LHSs (INCOMPARABLE and same variables)
        //
        // TODO: ad "containsAllVariablesOf": shouldn't we check multiset-inclusion instead of set-inclusion?
        static v_vector<TermList> lhsVector;
        lhsVector.clear();
        {
          TermList t0 = *eqLit->nthArgument(0);
          TermList t1 = *eqLit->nthArgument(1);
          switch (eqArgOrder) {
            case Ordering::INCOMPARABLE:
              ASS(!_preorderedOnly);  // would've skipped earlier already
              if (t0.containsAllVariablesOf(t1)) {
                lhsVector.push_back(t0);
              }
              if (t1.containsAllVariablesOf(t0)) {
                lhsVector.push_back(t1);
              }
              break;
            case Ordering::GREATER:
            case Ordering::GREATER_EQ:
              ASS(t0.containsAllVariablesOf(t1));
              lhsVector.push_back(t0);
              break;
            case Ordering::LESS:
            case Ordering::LESS_EQ:
              ASS(t1.containsAllVariablesOf(t0));
              lhsVector.push_back(t1);
              break;
            case Ordering::EQUAL:
              // there should be no equality literals with equal terms
              ASSERTION_VIOLATION;
            default:
              ASSERTION_VIOLATION;
          }
        }

        static DHSet<TermList> attempted;  // Terms we already attempted to demodulate
        attempted.reset();

        for (unsigned dli = 0; dli < cl->length(); ++dli) {
          Literal* dlit = (*cl)[dli];  // literal to be demodulated

          // Only demodulate in literals that are not matched by the subsumption check
          if (isMatched[dli]) {
            continue;
          }

          NonVariableIterator nvi(dlit);
          while (nvi.hasNext()) {
            TermList lhsS = nvi.next();  // named 'lhsS' because it will be matched against 'lhs'

            if (!attempted.insert(lhsS)) {
              // We have already tried to demodulate the term lhsS and did not
              // succeed (otherwise we would have returned from the function).
              // If we have tried the term lhsS, we must have tried to
              // demodulate also its subterms, so we can skip them too.
              nvi.right();
              continue;
            }

            if (SortHelper::getTermSort(lhsS, dlit) != eqSort) {
              continue;
            }

            ASS_LE(lhsVector.size(), 2);
            for (TermList lhs : lhsVector) {
              TermList rhs = EqHelper::getOtherEqualitySide(eqLit, lhs);

#if VDEBUG
              if (preordered) {
                if (eqArgOrder == Ordering::LESS) {
                  ASS_EQ(rhs, *eqLit->nthArgument(0));
                } else {
                  ASS_EQ(rhs, *eqLit->nthArgument(1));
                }
              }
#endif

              binder.reset();  // reset binder to state after subsumption check
              if (!MatchingUtils::matchTerms(lhs, lhsS, binder)) {
                continue;
              }

              TermList rhsS = binder.applyTo(rhs);
              ASS_EQ(lhsS, binder.applyTo(lhs));

              if (!preordered && ordering.compare(lhsS, rhsS) != Ordering::GREATER) {
                continue;
              }

              // Redundancy Check
              //
              // FSD is a simplification rule, so we want the simplified
              // premise (the right premise, cl) to be redundant after the
              // inference.
              //
              // Three conditions need to be satisfied:
              // 1. The premises (cl, mcl) must logically entail the conclusion,
              // 2. cl must be larger than the conclusion, and
              // 3. cl must be larger than the left premise mcl
              //    (to be completely precise, after applying the substitution Θ to mcl, i.e. mclΘ < cl).
              //
              // Conditions 1 and 2 are quite obvious (for 2, recall that lhsS > rhsS).
              // Condition 3 will be checked now.
              //
              // For perfomance reasons, we do not perform an exact check of mclΘ < cl.
              // Using the notation from above, we already know that C <= CΘ for the subsumption part.
              // If we can show that lΘ=rΘ < L[lΘ] \/ D, we can conclude that lΘ=rΘ \/ CΘ < L[lΘ] \/ C \/ D.
              //                     ^^^^^   ^^^^^                            ^^^^^^^^^^^   ^^^^^^^^^^^^^^^
              // (variable names:    eqLitS   dlit                                mclΘ             cl      )
              //
              // It is enough to find one literal M in L[lΘ] \/ D such that lΘ=rΘ < M.
              //
              // As an optimization, we first try to choose L as M because there are
              // easy-to-check criteria whether lΘ=rΘ < L[lΘ] holds. This is true if
              // one of the following holds:
              // 1. L is not an equality (as non-equality literals are always larger than equalities).
              // 2. L is s[lΘ] = t with s[lΘ] ≠ lΘ.
              //    Then s[lΘ] > lΘ (due to the subterm property of simplification orderings),
              //    and thus s[lΘ]=t > lΘ=rΘ.  (multiset extension of ordering: { s[lΘ], t } > { s[lΘ] } > { lΘ, rΘ }, because s[lΘ] > lΘ > rΘ)
              // 3. L is lΘ = t, but t is larger that rΘ.    (TODO: in the code actually: rΘ LESS or LESS_EQ than t)
              // If all these checks fail, we try to find a literal M in D such that lΘ=rΘ < M.
              if (!_allowIncompleteness) {
                if (!dlit->isEquality()) {
                  // non-equality literals are always larger than equality literals ==>  eqLitS < dlit
                  goto isRedundant;
                }
                if (lhsS != *dlit->nthArgument(0) && lhsS != *dlit->nthArgument(1)) {
                  // lhsS appears as argument to some function, e.g. f(lhsS) = t
                  // from subterm property of simplification ordering we know that lhsS < f(lhsS) and thus eqLitS < dlit
                  goto isRedundant;
                }
                // Now we are in the following situation:
                //
                //      eqLitS               dlit
                //    vvvvvvvvvvv          vvvvvvvv
                //    lhsS = rhsS \/ C     lhsS = t \/ CΘ \/ D
                //   ------------------------------------------
                //              rhsS = t \/ CΘ \/ D
                TermList t = EqHelper::getOtherEqualitySide(dlit, lhsS);
                if (t == rhsS) {
                  // in this case, eqLitS == dlit; and forward subsumption should have deleted the right premise already
                  ASS(binder.applyTo(eqLit) == dlit);  // eqLitS == dlit
                  ASS(!getOptions().forwardSubsumption());  // Note that _doSubsumption can still be true here because MLMatcher2 might find an FSD-match before the FS-match
                  premises = pvi(getSingletonIterator(mcl));
                  env.statistics->forwardSubsumed++;
                  return true;
                }
                Ordering::Result r_cmp_t = ordering.compare(rhsS, t);
                if (r_cmp_t == Ordering::LESS || r_cmp_t == Ordering::LESS_EQ) {
                  ASS(r_cmp_t == Ordering::LESS);  // TODO really not sure why we need to allow LESS_EQ in the condition
                  // rhsS < t implies eqLitS < dlit
                  goto isRedundant;
                }
                // We could not show redundancy with dlit alone,
                // so now we have to look at the other literals of cl
                Literal* eqLitS = Literal::createEquality(true, lhsS, rhsS, eqSort);
                ASS_EQ(eqLitS, binder.applyTo(eqLit));
                for (unsigned li2 = 0; li2 < cl->length(); li2++) {
                  // skip dlit (already checked with r_cmp_t above) and matched literals (i.e., CΘ)
                  if (dli != li2 && !isMatched[li2]) {
                    Literal* lit2 = (*cl)[li2];
                    if (ordering.compare(eqLitS, lit2) == Ordering::LESS) {  // TODO why do we only allow LESS here, while for dlit (above) we also allow LESS_EQ???
                      // we found that eqLitS < lit2; and thus mcl < cl => after inference, cl is redundant
                      goto isRedundant;
                    }
                  }
                }
                // cl might not be redundant after the inference, possibly leading to incompleteness => skip
                continue;
              }  // if (!_allowIncompleteness)
isRedundant:

              /**
               * Step 4: found application of FSD; now create the conclusion
               */
              Literal* newLit = EqHelper::replace(dlit, lhsS, rhsS);
              ASS_EQ(ordering.compare(lhsS, rhsS), Ordering::GREATER);
              ASS_EQ(ordering.compare(dlit, newLit), Ordering::GREATER);

              if (EqHelper::isEqTautology(newLit)) {
                env.statistics->forwardSubsumptionDemodulationsToEqTaut++;
                premises = pvi(getSingletonIterator(mcl));
                replacement = nullptr;
                return true;
              }

              Inference* inference = new Inference2(Inference::FORWARD_SUBSUMPTION_DEMODULATION, cl, mcl);
              Unit::InputType inputType = std::max(cl->inputType(), mcl->inputType());

              Clause* newCl = new(cl->length()) Clause(cl->length(), inputType, inference);

              for (unsigned i = 0; i < cl->length(); ++i) {
                if (i == dli) {
                  (*newCl)[i] = newLit;
                } else {
                  (*newCl)[i] = (*cl)[i];
                }
              }

              newCl->setAge(cl->age());
              env.statistics->forwardSubsumptionDemodulations++;

              premises = pvi(getSingletonIterator(mcl));
              replacement = newCl;

#if FSD_LOG_INFERENCES
              env.beginOutput();
              env.out() << "\% Begin Inference \"FSDv2-" << newCl->number() << "\"\n";
              env.out() << "\% eqLit: " << eqLit->toString() << "\n";
              env.out() << "\% eqLitS: " << binder.applyTo(eqLit)->toString() << "\n";
              env.out() << "\% dlit: " << binder.applyTo(dlit)->toString() << "\n";
              TPTPPrinter tptp;
              // NOTE: do not output the splitLevels here, because those will be set for newCl only later
              tptp.printWithRole("side_premise_mcl", "hypothesis", mcl,   false);
              tptp.printWithRole("main_premise_cl ", "hypothesis", cl,    false);
              tptp.printWithRole("conclusion      ", "conjecture", newCl, false);
              env.out() << "\% End Inference \"FSDv2-" << newCl->number() << "\"" << std::endl;
              env.endOutput();
#endif

              return true;
            } // for lhs
          } // while (nvi.hasNext())
        } // for dli
      } // for (numMatches)
    } // while (rit.hasNext)
  } // for (li)

  return false;
}
