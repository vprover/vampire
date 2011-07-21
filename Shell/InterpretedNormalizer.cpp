/**
 * @file InterpretedNormalizer.cpp
 * Implements class InterpretedNormalizer.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"

#include "InterpretedNormalizer.hpp"

namespace Shell
{

class InterpretedNormalizer::NLiteralTransformer : private TermTransformer
{
public:
  void apply(Literal* lit, bool& constantRes, Literal*& litRes, bool& boolRes)
  {
    if(theory->isInterpretedPredicate(lit)) {
      Interpretation itp = theory->interpretPredicate(lit);
      if(isTrivialInterpretation(itp)) {
	constantRes = true;
	boolRes = lit->isPositive();
	return;
      }
    }
    constantRes = false;
    litRes = transform(lit);
  }
protected:
  using TermTransformer::transform;

  virtual TermList transform(TermList trm)
  {
    CALL("InterpretedNormalizer::NLiteralTransformer::transform");

    if(!theory->isInterpretedFunction(trm)) { return trm; }
    Interpretation itp = theory->interpretFunction(trm);
    if(!isTrivialInterpretation(itp)) { return trm; }
    Term* t = trm.term();
    ASS_EQ(t->arity(),1);
    return *t->nthArgument(0);
  }
};

class InterpretedNormalizer::NFormulaTransformer : public FormulaTransformer
{
protected:
  virtual Formula* applyLiteral(Formula* f)
  {
    CALL("applyLiteral");

    Literal* lit = f->literal();
    bool isConst;
    Literal* newLit;
    bool newConst;
    _litTransf.apply(lit, isConst, newLit, newConst);
    if(isConst) {
      return new Formula(newConst);
    }
    if(newLit==lit) { return f; }
    return new AtomicFormula(newLit);
  }

private:
  NLiteralTransformer _litTransf;
};

//////////////////////////
// InterpretedNormalizer
//

void InterpretedNormalizer::apply(UnitList*& units)
{
  CALL("InterpretedNormalizer::apply");

  NFormulaTransformer ftransf;
  FTFormulaUnitTransformer<NFormulaTransformer> futransf(Inference::EVALUATION, ftransf);

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
      }
    }
    else {
      FormulaUnit* fu = static_cast<FormulaUnit*>(u);
      FormulaUnit* fu1 = futransf.transform(fu);
      if(fu!=fu1) {
	uit.replace(fu1);
      }
    }
  }
}

Clause* InterpretedNormalizer::apply(Clause* cl)
{
  CALL("InterpretedNormalizer::isTrivialInterpretation");

  static NLiteralTransformer litTransf;

  static LiteralStack lits;
  lits.reset();
  unsigned clen = cl->length();
  bool modified = false;

  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*cl)[i];

    bool isConst;
    Literal* newLit;
    bool newConst;
    litTransf.apply(lit, isConst, newLit, newConst);

    if(isConst) {
      modified = true;
      if(newConst) {
	return 0;
      }
      continue;
    }
    if(newLit!=lit) {
      modified = true;
    }
    lits.push(newLit);
  }
  if(!modified) {
    return cl;
  }

  Clause* res = Clause::fromStack(lits, cl->inputType(),
      new Inference1(Inference::EVALUATION, cl));
  return res;
}

bool InterpretedNormalizer::isTrivialInterpretation(Interpretation itp)
{
  CALL("InterpretedNormalizer::isTrivialInterpretation");

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
    return true;

  default:
    return false;
  }
}

}
