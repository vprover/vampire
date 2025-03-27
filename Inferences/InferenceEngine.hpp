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
 * @file InferenceEngine.hpp
 * Defines class InferenceEngine
 *
 */

#ifndef __InferenceEngine__
#define __InferenceEngine__

#include "Forwards.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"

#include "Lib/VirtualIterator.hpp"
#include "Lib/List.hpp"

#include "Lib/Allocator.hpp"
#include "Kernel/Inference.hpp"
#include "Lib/Coproduct.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#if VDEBUG
#include "Indexing/Index.hpp"
#endif

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;
using namespace Shell;

/**
 * InferenceEngine is a base class for classes representing possible
 * inferences -- generating inferences and forward and backward
 * simplifications. These inferences will take only the non-propositional
 * part of the clause into account. The caller must take care of the
 * propositional part, or be sure that the propositional part is not
 * being used at all.
 */
class InferenceEngine
{
public:
  InferenceEngine() : _salg(0) {}
  virtual ~InferenceEngine()
  {
    //the object has to be detached before destruction
    ASS(!_salg);
  }
  virtual void attach(SaturationAlgorithm* salg)
  {
    ASS(!_salg);
    _salg=salg;
  }
  virtual void detach()
  {
    ASS(_salg);
    _salg=0;
  }

  /**
   * Return true if inference engine is attached to a saturation algorithm
   */
  bool attached() const { return _salg; }

  virtual const Options& getOptions() const;
#if VDEBUG
  /**
   * Normally indices are managed by `IndexManager`, which is contained in the saturation algorithm class.
   * This is unfortunate for unit testing, as it requires to instantiate the whole SaturationAlgorithm
   * machinery for unit testing a single rule if that rule uses a term index. In order to circumvent this
   * issue we add this method in debug mode.
   * */
  virtual void setTestIndices(Stack<Indexing::Index*> const&) {}
#endif // VDEBUG
protected:
  SaturationAlgorithm* _salg;
};

/** A generating inference that might make its major premise redundant. */
class SimplifyingGeneratingInference
: public InferenceEngine
{
public:

  /** result of applying the inference */
  struct ClauseGenerationResult {
    /** the generated clauses */
    ClauseIterator clauses;
    /** tells whether the major premise of the application of the rule should be deleted from the search space. */
    bool premiseRedundant;
    static ClauseGenerationResult nothing() {
      return ClauseGenerationResult { .clauses = ClauseIterator::getEmpty(), .premiseRedundant = false, };
    }
  };


  /**
   * Applies this rule to the clause, and returns an iterator over the resulting clauses, 
   * as well as the information wether the premise was made redundant.
   */
  virtual ClauseGenerationResult generateSimplify(Clause* premise) = 0;
  /** TODO */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) = 0;
};


class GeneratingInferenceEngine
: public SimplifyingGeneratingInference
{

public:
  virtual ClauseIterator generateClauses(Clause* premise) = 0;

  ClauseGenerationResult generateSimplify(Clause* premise) override
  { return { .clauses = generateClauses(premise), 
             .premiseRedundant = false, }; }
};

class ImmediateSimplificationEngine
: public InferenceEngine
{
public:
  /**
   * Perform an immediate simplification on @b cl and return
   * the result. If the simplification is not applicable, return
   * @b cl, if @b cl should be deleted, return 0.
   *
   * When the simplification yields a simplified clause, repeated
   * run of the method on resulting clause can lead to another
   * simplification.
   *
   * A trivial simplification does not depend on any other clauses.
   * The simplified clause, if any, will have just one inference
   * premise, which will be equal to @b cl.
   *
   * An example of a trivial simplification is deletion of duplicate
   * literals.
   */
  virtual ClauseIterator simplifyMany(Clause* cl){ NOT_IMPLEMENTED; } ;
  virtual Clause* simplify(Clause* cl) = 0;
};

/**
 * A SimplifyingGeneratingInference that generates at most one clause. 
 * 
 * Such an inference can be used as ImmediateSimplificationEngine, by calling asISE(). 
 * @warning When used as ISE non-redundant clauses might be deleted from the search space. Therefore completeness might be lost!
 */
class SimplifyingGeneratingInference1
: public SimplifyingGeneratingInference
, ImmediateSimplificationEngine
{
public:
  struct Result 
  {
    Clause* simplified;
    bool premiseRedundant;

    inline static Result tautology() 
    { return { .simplified = nullptr, .premiseRedundant = true, }; }

    inline static Result nop(Clause* cl) 
    { return { .simplified = cl, .premiseRedundant = false, }; }

  };

  ClauseGenerationResult generateSimplify(Clause* cl) override;

  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) override 
  { return pvi(dropElementType(range(0,1))); }

  /** 
   * Turns this SimplifyingGeneratingInference1 into and ImmediateSimplificationEngine. 
   * The resulting ImmediateSimplificationEngine will call simplify(Clause*, bool doOrderingCheck) with 
   * doOrderingCheck = false, and ignore the value of SimplifyingGeneratingInference1::Result::premiseRedundant.
   *
   * @warning the resulting ImmediateSimplificationEngine might not conform with the simplification ordering, which means that non-redundant clauses might be deleted, which yields a loss of completeness!
   */
  ImmediateSimplificationEngine& asISE();

  virtual void attach(SaturationAlgorithm* salg) override { SimplifyingGeneratingInference::attach(salg); }
  virtual void detach() override { SimplifyingGeneratingInference::detach(); }
  
protected:

  /** returns the simplified clause and whether the premise was made redundant. 
   *
   * \param doOrderingCheck is used in order to be able to skip any ordering 
   *      checks (which is an expensive computation), when Result::premiseRedundant is ignored anyways. 
   * \param cl is the clause to be simplified. if the clause is a tautology, Result::tautology() should be returned.
   */
  virtual Result simplify(Clause* cl, bool doOrderingCheck) = 0;
private:
  Clause* simplify(Clause* cl) override;
};

/**
 * A SimplifyingGeneratingInference1 that is applied literal by literal
 */
class SimplifyingGeneratingLiteralSimplification
: public SimplifyingGeneratingInference1
{

public:
  class Result : public Lib::Coproduct<Literal*, bool> 
  {
  private:
    explicit Result(Coproduct&& l) : Coproduct(std::move(l)) {}
  public:
    using super = Lib::Coproduct<Literal*, bool>;
    /**
     * returns whether the result is a trivial literal (top or bot)
     */
    inline bool isConstant() const& { return is<1>(); }
    inline bool isLiteral() const& { return is<0>(); }
    inline bool unwrapConstant() const& { return unwrap<1>(); }
    inline Literal* unwrapLiteral() const& { return unwrap<0>(); }
    inline static Result constant(bool b) { return Result(Coproduct::template variant<1>(b)); }
    inline static Result literal(Literal* b) { return Result(Coproduct::template variant<0>(b)); }
  };

protected:
  SimplifyingGeneratingLiteralSimplification(InferenceRule rule, Ordering& ordering);
  virtual Result simplifyLiteral(Literal* l) = 0;
  SimplifyingGeneratingInference1::Result simplify(Clause* cl, bool doOrderingCheck) override;

private:
  Ordering* _ordering;
  const InferenceRule _rule;
};

class SimplificationEngine
: public InferenceEngine
{
public:
  /**
   * Perform simplification on @b cl
   *
   * The difference between this an immediate simplification is that it is delayed 
   * in the saturation loop
   */
  virtual ClauseIterator perform(Clause* cl) = 0;
};

class ForwardSimplificationEngine
: public InferenceEngine
{
public:
  /**
   * Perform forward simplification on @b cl
   *
   * Return true if the simplification is applicable on @b cl,
   * set @b replacement to a replacing clause if there is one (otherwise keep @b replacement = nullptr)
   *
   * @b premises will contain clauses that justify the simplification
   * performed.
   */
  virtual bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) = 0;

  virtual const char* name() const = 0;
};


struct BwSimplificationRecord
{
  BwSimplificationRecord() {}
  BwSimplificationRecord(Clause* toRemove)
  : toRemove(toRemove), replacement(0) {}
  BwSimplificationRecord(Clause* toRemove, Clause* replacement)
  : toRemove(toRemove), replacement(replacement) {}

  Clause* toRemove;
  Clause* replacement;
};
typedef VirtualIterator<BwSimplificationRecord> BwSimplificationRecordIterator;

class BackwardSimplificationEngine
: public InferenceEngine
{
public:
  /**
   * Perform backward simplification with @b premise.
   *
   * Descendant classes should pay attention to the possibility that
   * the premise could be present in the simplification indexes at
   * the time of call to this method.
   */
  virtual void perform(Clause* premise, BwSimplificationRecordIterator& simplifications) = 0;
};


class DummyGIE
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise) override
  { return ClauseIterator::getEmpty(); }

  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) override
  { return pvi(dropElementType(range(0,0))); }

};

template<class... Args>
class TupleISE
: public ImmediateSimplificationEngine
{
  std::tuple<Args...> _self;
public:
  TupleISE(Args... args) : _self(std::move(args)...) { }
  auto iter() { return std::apply([](auto&... args) { return iterItems(static_cast<ImmediateSimplificationEngine*>(&args)...); }, _self); }
  Clause* simplify(Clause* premise) override {
    return iter()
          .map([&](auto* rule) { return rule->simplify(premise); })
          .find([&](auto concl) { return concl != premise; })
          .unwrapOr(premise);
  }
};

template<class... Args>
TupleISE<Args...> tupleISE(Args... args) 
{ return TupleISE<Args...>(std::move(args)...); }




class CompositeISE
: public ImmediateSimplificationEngine
{
public:
  CompositeISE() : _inners(0), _innersMany(0) {}
  virtual ~CompositeISE();
  void addFront(ImmediateSimplificationEngine* fse);
  void addFrontMany(ImmediateSimplificationEngine* fse);
  Clause* simplify(Clause* cl) override;
  ClauseIterator simplifyMany(Clause* cl) override;
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
private:
  typedef List<ImmediateSimplificationEngine*> ISList;
  ISList* _inners;
  ISList* _innersMany;
};

class CompositeGIE
: public GeneratingInferenceEngine
{
public:
  CompositeGIE() : _inners(0) {}
  virtual ~CompositeGIE();
  void addFront(GeneratingInferenceEngine* fse);
  ClauseIterator generateClauses(Clause* premise) override;
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) override
  { return pvi(dropElementType(range(0,0))); }
private:
  typedef List<GeneratingInferenceEngine*> GIList;
  GIList* _inners;
};


class CompositeSGI
: public SimplifyingGeneratingInference
{
public:
  CompositeSGI() : _simplifiers(), _generators() {}
  virtual ~CompositeSGI();
  void push(SimplifyingGeneratingInference*);
  void push(GeneratingInferenceEngine*);
  ClauseGenerationResult generateSimplify(Clause* premise) override;
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) override
  { return pvi(dropElementType(range(0,0))); }
private:
  Stack<SimplifyingGeneratingInference*> _simplifiers;
  Stack<GeneratingInferenceEngine*> _generators;
};

//removes clauses which define choice operators
class ChoiceDefinitionISE
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;

  bool isPositive(Literal* lit);
 
  bool is_of_form_xy(Literal* lit,  TermList& x);
  bool is_of_form_xfx(Literal* lit, TermList x, TermList& f);
};

class DuplicateLiteralRemovalISE
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

class TautologyDeletionISE2
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

class TrivialInequalitiesRemovalISE
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

};

#endif /*__InferenceEngine__*/
