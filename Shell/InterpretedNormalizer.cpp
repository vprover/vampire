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
 * @file InterpretedNormalizer.cpp
 * Implements class InterpretedNormalizer.
 */

#include "Lib/Environment.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Property.hpp"

#include "InterpretedNormalizer.hpp"

namespace Shell
{

using namespace std;

/**
 * Base term transforming class
 */
class InterpretedNormalizer::FunctionTranslator
{
public:
  virtual ~FunctionTranslator() {}

  virtual TermList translate(Term* trm) = 0;
};

/**
 * Class for translating functions with rounding suffixes _t and _f
 */
class InterpretedNormalizer::RoundingFunctionTranslator : public FunctionTranslator
{
public:
  RoundingFunctionTranslator(Interpretation origf, Interpretation newf, Interpretation roundf)
  {
    _origFun = env.signature->getInterpretingSymbol(origf);
    _newFun = env.signature->getInterpretingSymbol(newf);
    _roundingFun = env.signature->getInterpretingSymbol(roundf);

  }

  virtual TermList translate(Term* trm)
  {
    ASS_EQ(trm->functor(), _origFun);

    TermList arg1 = trm->termArg(0);
    TermList arg2 = trm->termArg(1);
    TermList newF(Term::create2(_newFun, arg1, arg2));
    TermList res(Term::create1(_roundingFun,newF));
    return res;
  }

  /** Function that is being rewritten by this object */
  unsigned srcFunc() const { return _origFun; }
private:

  unsigned _origFun;
  unsigned _newFun;
  unsigned _roundingFun;
};

/**
 * Class for transforming terms suc(t) into t+1
 * suc not in TPTP
 */
class InterpretedNormalizer::SuccessorTranslator : public FunctionTranslator
{
public:
  SuccessorTranslator()
  {
    _succFun = env.signature->getInterpretingSymbol(Theory::INT_SUCCESSOR);
    _plusFun = env.signature->getInterpretingSymbol(Theory::INT_PLUS);
    _one = TermList(theory->representConstant(IntegerConstantType(1)));
  }

  virtual TermList translate(Term* trm)
  {
    ASS_EQ(trm->functor(), _succFun);

    TermList arg = trm->termArg(0);
    TermList res(Term::create2(_plusFun, arg, _one));
    return res;
  }

  /** Function that is being rewritten by this object */
  unsigned srcFunc() const { return _succFun; }
private:

  unsigned _succFun;
  unsigned _plusFun;
  TermList _one;
};

/**
 * Class for transforming terms (t-u) into (t+(-u))
 */
class InterpretedNormalizer::BinaryMinusTranslator : public FunctionTranslator
{
public:
  BinaryMinusTranslator(Interpretation bMinus, Interpretation plus, Interpretation uMinus)
  {
    _bMinusFun = env.signature->getInterpretingSymbol(bMinus);
    _plusFun = env.signature->getInterpretingSymbol(plus);
    _uMinusFun = env.signature->getInterpretingSymbol(uMinus);
  }

  virtual TermList translate(Term* trm)
  {
    ASS_EQ(trm->functor(), _bMinusFun);

    TermList arg1 = trm->termArg(0);
    TermList arg2 = trm->termArg(1);
    TermList negArg2(Term::create1(_uMinusFun, arg2));
    TermList res(Term::create2(_plusFun, arg1, negArg2));
    return res;
  }

  /** Function that is being rewritten by this object */
  unsigned srcFunc() const { return _bMinusFun; }
private:

  unsigned _bMinusFun;
  unsigned _plusFun;
  unsigned _uMinusFun;
};

/**
 * Class whose instances are to be used for translating one type of inequality to enother
 */
class InterpretedNormalizer::IneqTranslator
{
public:
  IneqTranslator(Interpretation src, Interpretation tgt, bool swapArguments, bool reversePolarity)
   : _swapArguments(swapArguments), _reversePolarity(reversePolarity)
  {
    _srcPred = env.signature->getInterpretingSymbol(src);
    _tgtPred = env.signature->getInterpretingSymbol(tgt);
    ASS_EQ(env.signature->predicateArity(_srcPred), 2);
    ASS_EQ(env.signature->predicateArity(_tgtPred), 2);

  }

  /** Predicate that is being rewritten by this object */
  unsigned srcPred() const { return _srcPred; }

  Literal* apply(Literal* lit)
  {
    ASS_EQ(lit->functor(), _srcPred);

    TermList args[2] = { lit->termArg(0), lit->termArg(1) };
    if(_swapArguments) { swap(args[0], args[1]); }
    bool polarity = lit->isPositive() ^ _reversePolarity;

    return Literal::create(_tgtPred, 2, polarity, args);
  }

private:
  unsigned _srcPred;
  unsigned _tgtPred;
  bool _swapArguments;
  bool _reversePolarity;
};

/**
 * Class that performs literal transformations
 */
class InterpretedNormalizer::NLiteralTransformer : public BottomUpTermTransformer
{
public:
  NLiteralTransformer()
  : _ineqTransls(env.signature->predicates()),
    _fnTransfs(env.signature->functions())
  {
    // from, to, swap, reverse_pol 
    addIneqTransformer(Theory::INT_LESS_EQUAL, 	  Theory::INT_LESS, true, true);
    addIneqTransformer(Theory::INT_GREATER, 	  Theory::INT_LESS, true, false);
    addIneqTransformer(Theory::INT_GREATER_EQUAL, Theory::INT_LESS, false, true);

    addIneqTransformer(Theory::RAT_LESS_EQUAL, 	  Theory::RAT_LESS, true, true);
    addIneqTransformer(Theory::RAT_GREATER,	  Theory::RAT_LESS, true, false);
    addIneqTransformer(Theory::RAT_GREATER_EQUAL, Theory::RAT_LESS, false, true);

    addIneqTransformer(Theory::REAL_LESS_EQUAL,	  Theory::REAL_LESS, true, true);
    addIneqTransformer(Theory::REAL_GREATER,	  Theory::REAL_LESS, true, false);
    addIneqTransformer(Theory::REAL_GREATER_EQUAL,Theory::REAL_LESS, false, true);

    addMinusTransformer(Theory::INT_MINUS, Theory::INT_PLUS, Theory::INT_UNARY_MINUS);
    addMinusTransformer(Theory::RAT_MINUS, Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS);
    addMinusTransformer(Theory::REAL_MINUS, Theory::REAL_PLUS, Theory::REAL_UNARY_MINUS);

    addSuccessorTransformer();

    addRoundingFunctionTransformer(Theory::RAT_QUOTIENT_T, Theory::RAT_QUOTIENT, Theory::RAT_TRUNCATE);
    addRoundingFunctionTransformer(Theory::RAT_QUOTIENT_F, Theory::RAT_QUOTIENT, Theory::RAT_FLOOR);
    addRoundingFunctionTransformer(Theory::REAL_QUOTIENT_T, Theory::REAL_QUOTIENT, Theory::REAL_TRUNCATE);
    addRoundingFunctionTransformer(Theory::REAL_QUOTIENT_F, Theory::REAL_QUOTIENT, Theory::REAL_FLOOR);

    //addRoundingFunctionTransformer(Theory::RAT_REMAINDER_T, Theory::RAT_REMAINDER, Theory::RAT_TRUNCATE);
    //addRoundingFunctionTransformer(Theory::RAT_QUOTIENT_F, Theory::RAT_QUOTIENT, Theory::RAT_FLOOR);
    //addRoundingFunctionTransformer(Theory::REAL_QUOTIENT_T, Theory::REAL_QUOTIENT, Theory::REAL_TRUNCATE);
    //addRoundingFunctionTransformer(Theory::REAL_QUOTIENT_F, Theory::REAL_QUOTIENT, Theory::REAL_FLOOR);
  }

  void apply(Literal* lit, bool& constantRes, Literal*& litRes, bool& boolRes)
  {
    if (!lit->isEquality() && theory->isInterpretedPredicate(lit->functor()))
    {
      Interpretation itp = theory->interpretPredicate(lit);
      if(isTrivialInterpretation(itp)) {
        constantRes = true;
        boolRes = lit->isPositive();
        return;
      }
    }

    constantRes = false;
    litRes = transformLiteral(lit);
    unsigned pred = litRes->functor();
    IneqTranslator* transl = getIneqTranslator(pred);
    if(transl) {
      litRes = transl->apply(litRes);
    }
  }

  Formula* transform(Formula* f) override;

protected:
  using BottomUpTermTransformer::transform;

  TermList transformSubterm(TermList trm) override
  {
    // sorts can never contain interpreted functions
    // this is a stopgap solution until PR that changes how termTransformer works
    // is merged
    // WARNING current implementation entails unecessary traversal of sort subterms
    if(trm.isTerm() && trm.term()->isSort()) return trm;

  start:
    if(theory->isInterpretedFunction(trm)) {
      Interpretation itp = theory->interpretFunction(trm);
      if(isTrivialInterpretation(itp)) {
	Term* t = trm.term();
	ASS_EQ(t->arity(),1);
	return t->termArg(0);
      }
    }
    if(trm.isTerm()) {
      Term* t = trm.term();
      unsigned func = t->functor();
      FunctionTranslator* transl = getFnTranslator(func);
      if(transl) {
	trm = transl->translate(t);
	goto start;
      }
    }
    return trm;
  }

private:

  /**
   * Ensure that binary minus @c bMinus will be replaced by combination of
   * plus operation @c plus and unary minus @c uMinus
   */
  void addMinusTransformer(Interpretation bMinus, Interpretation plus, Interpretation uMinus)
  {
    if(!env.signature->haveInterpretingSymbol(bMinus)) {
      return; //the symbol to be transformed doesn't exist, so we don't need to worry
    }
    BinaryMinusTranslator* transl = new BinaryMinusTranslator(bMinus, plus, uMinus);
    unsigned func = transl->srcFunc();
    ASS(!_fnTransfs[func])
    _fnTransfs[func] = transl;
  }

  /**
   * Ensure the INT_SUCCESSOR operation is rewritten to X+1
   */
  void addSuccessorTransformer()
  {
    if(!env.signature->haveInterpretingSymbol(Theory::INT_SUCCESSOR)) {
      return; //the symbol to be transformed doesn't exist, so we don't need to worry
    }
    SuccessorTranslator* transl = new SuccessorTranslator();
    unsigned func = transl->srcFunc();
    ASS(!_fnTransfs[func])
    _fnTransfs[func] = transl;
  }

  /**
   * Ensure the rounding function origF will be replaced by newF and roundF 
   */
  void addRoundingFunctionTransformer(Interpretation origF, Interpretation newF, Interpretation roundF)
  {
    if(!env.signature->haveInterpretingSymbol(origF)) {
      return; //the symbol to be transformed doesn't exist, so we don't need to worry
    }
    RoundingFunctionTranslator* transl = new RoundingFunctionTranslator(origF,newF,roundF);
    unsigned func = transl->srcFunc();
    ASS(!_fnTransfs[func])
    _fnTransfs[func] = transl;
  }

  /**
   * Ensure that inequality @c from will be replaced by inequality @c to.
   * The arguments @c swapArguments and @c reversePolarity specify how the
   * replacement should be done.
   */
  void addIneqTransformer(Interpretation from, Interpretation to, bool swapArguments, bool reversePolarity)
  {
    if(!env.signature->haveInterpretingSymbol(from)) {
      return; //the symbol to be transformed doesn't exist, so we don't need to worry
    }
    IneqTranslator* transl = new IneqTranslator(from, to, swapArguments, reversePolarity);
    unsigned pred = transl->srcPred();
    ASS(!_ineqTransls[pred])
    _ineqTransls[pred] = transl;
  }

  /**
   * Return object that translates occurrences of function @c func, or zero
   * if there isn't any.
   */
  FunctionTranslator* getFnTranslator(unsigned func)
  {
    if(_fnTransfs.size()<=func) { return 0; }
    return _fnTransfs[func].ptr();
  }

  /**
   * Return object that translates occurrences of inequalities with predicate @c pred,
   * or zero if there isn't any.
   */
  IneqTranslator* getIneqTranslator(unsigned ineq)
  {
    if(_ineqTransls.size()<=ineq) { return 0; }
    return _ineqTransls[ineq].ptr();
  }

  /** inequality translators at positions of their predicate numbers */
  DArray<ScopedPtr<IneqTranslator> > _ineqTransls;
  /** inequality translators at positions of their predicate numbers */
  DArray<ScopedPtr<FunctionTranslator> > _fnTransfs;
};

/**
 * Class that uses @c NLiteralTransformer to perform transformations on formulas
 */
class InterpretedNormalizer::NFormulaTransformer : public FormulaTransformer
{
public:
  NFormulaTransformer(NLiteralTransformer* litTransf) : _litTransf(litTransf) {}

protected:
  /**
   * Transfor atomic formula
   *
   * The rest of transformations is done by the @c FormulaTransformer ancestor.
   */
  virtual Formula* applyLiteral(Formula* f)
  {
    Literal* lit = f->literal();
    bool isConst;
    Literal* newLit;
    bool newConst;
    _litTransf->apply(lit, isConst, newLit, newConst);
    if(isConst) {
      return new Formula(newConst);
    }
    if(newLit==lit) { return f; }
    return new AtomicFormula(newLit);
  }

private:
  NLiteralTransformer* _litTransf;
};

Formula* InterpretedNormalizer::NLiteralTransformer::transform(Formula* f)
{
  NFormulaTransformer ttft(this);
  return ttft.transform(f);
}

//////////////////////////
// InterpretedNormalizer
//

InterpretedNormalizer::InterpretedNormalizer()
: _litTransf(new NLiteralTransformer())
{
}

InterpretedNormalizer::~InterpretedNormalizer()
{
  delete _litTransf;
}

void InterpretedNormalizer::apply(Problem& prb)
{
  if(apply(prb.units())) {
    prb.invalidateByRemoval();
  }
}

/**
 * Apply the interpreted normalization to @c units.
 * Return true iff any of the units was modified.
 */
bool InterpretedNormalizer::apply(UnitList*& units)
{
  NFormulaTransformer ftransf(_litTransf);
  FTFormulaUnitTransformer<NFormulaTransformer> futransf(InferenceRule::THEORY_NORMALIZATION, ftransf);

  bool modified = false;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      Clause* cl = static_cast<Clause*>(u);
      Clause* cl1 = apply(cl);
      if(cl!=cl1) {
	if(cl1) {
	  uit.replace(cl1);
	}
	else {
	  uit.del();
	}
	modified = true;
      }
    }
    else {
      FormulaUnit* fu = static_cast<FormulaUnit*>(u);
      FormulaUnit* fu1 = futransf.transform(fu);
      if(fu!=fu1) {
	      uit.replace(fu1);
	      modified = true;
      }
    }
  }
  return modified;
}

Clause* InterpretedNormalizer::apply(Clause* cl)
{
  static LiteralStack lits;
  lits.reset();
  unsigned clen = cl->length();
  bool modified = false;

  for(unsigned i=0; i<clen; i++) {
    Literal* orig = (*cl)[i];

    bool isConst;
    Literal* newLit;
    bool newConst;
    _litTransf->apply(orig, isConst, newLit, newConst);

    if(isConst) {
      modified = true;
      if(newConst) {
	return 0;
      }
      continue;
    }
    if(newLit != orig) {
      modified = true;
    }
    lits.push(newLit);
  }
  if(!modified) {
    return cl;
  }

  Clause* res = Clause::fromStack(lits,
      FormulaClauseTransformation(InferenceRule::THEORY_NORMALIZATION, cl));
  // DBG(*cl, " ==> ", *res)
  return res;
}

/**
 * Return true if interpretatioin @c itp is trivial and shold just be
 * removed as an identity (in case of functions), or replaced by $true
 * (in case of predicates)
 */
bool InterpretedNormalizer::isTrivialInterpretation(Interpretation itp)
{
  switch(itp) {
  case Theory::INT_IS_INT:
  case Theory::INT_IS_RAT:
  case Theory::INT_IS_REAL:
  case Theory::RAT_IS_RAT:
  case Theory::RAT_IS_REAL:
  case Theory::REAL_IS_REAL:

  case Theory::INT_TO_INT:
  case Theory::RAT_TO_RAT:
  case Theory::REAL_TO_REAL:

  case Theory::INT_TRUNCATE:
  case Theory::INT_FLOOR:
  case Theory::INT_CEILING:
  case Theory::INT_ROUND:
    return true;

  default:
    return false;
  }
}

}
