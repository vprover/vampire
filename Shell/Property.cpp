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
 * @file Property.cpp (syntactic properties of problems)
 *
 * @since 06/06/2001 Manchester
 * @author Andrei Voronkov
 * @since 17/07/2003 Manchester, changed to new representation
 */


#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/TermIterators.hpp"

#include "Options.hpp"
#include "FunctionDefinition.hpp"
#include "Property.hpp"
#include "SubexpressionIterator.hpp"
#include "Kernel/NumTraits.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;
namespace Shell {


/**
 * Initialize Property. Must be applied to the preprocessed problem.
 *
 * @since 29/06/2002, Manchester
 */
Property::Property()
  : _goalClauses(0),
    _axiomClauses(0),
    _positiveEqualityAtoms(0),
    _equalityAtoms(0),
    _atoms(0),
    _goalFormulas(0),
    _axiomFormulas(0),
    _subformulas(0),
    _unitGoals(0),
    _unitAxioms(0),
    _hornGoals(0),
    _hornAxioms(0),
    _equationalClauses(0),
    _pureEquationalClauses(0),
    _groundUnitAxioms(0),
    _positiveAxioms(0),
    _groundPositiveAxioms(0),
    _groundGoals(0),
    _maxFunArity(0),
    _maxPredArity(0),
    _maxTypeConArity(0),
    _totalNumberOfVariables(0),
    _maxVariablesInClause(0),
    _props(0),
    _hasInterpreted(false),
    _hasNonDefaultSorts(false),
    _sortsUsed(0),
    _hasFOOL(false),
    _hasArrowSort(false),
    _hasApp(false),
    _hasAppliedVar(false),
    _hasBoolVar(false),
    _hasLogicalProxy(false),
    _hasLambda(false),
    _hasPolymorphicSym(false),
    _hasAnswerLiteral(false),
    _quantifiesOverPolymorphicVar(false),
    _onlyFiniteDomainDatatypes(true),
    _knownInfiniteDomain(false),
    _allClausesGround(true),
    _allNonTheoryClausesGround(true),
    _allQuantifiersEssentiallyExistential(true),
    _hasNumeralsInt(false),
    _hasNumeralsRat(false),
    _hasNumeralsReal(false),
    _nonLinearInt(false),
    _nonLinearRat(false),
    _nonLinearReal(false),
    _smtlibLogic(SMTLIBLogic::UNDEFINED)
{
  _interpretationPresence.init(Theory::instance()->numberOfFixedInterpretations(), false);
} // Property::Property

/**
 * Create a new property, scan the units with it and return the property.
 * @since 22/07/2011 Manchester
 */
Property* Property::scan(UnitList* units)
{
  // a bit of a hack, these counts belong in Property
  for(unsigned f=0;f<env.signature->functions();f++){ 
    env.signature->getFunction(f)->resetUsageCnt(); 
    env.signature->getFunction(f)->resetUnitUsageCnt(); 
   }
  for(unsigned p=0;p<env.signature->predicates();p++){ 
    env.signature->getPredicate(p)->resetUsageCnt(); 
    env.signature->getPredicate(p)->resetUnitUsageCnt(); 
   }

  Property* prop = new Property;
  prop->add(units);
  return prop;
} // Property::scan

/**
 * Add units and modify an existing property.
 * @since 29/06/2002 Manchester
 */
void Property::add(UnitList* units)
{
  UnitList::Iterator us(units);
  while (us.hasNext()) {
    scan(us.next());
  }

  if (_allClausesGround && _allQuantifiersEssentiallyExistential) {
    addProp(PR_ESSENTIALLY_GROUND);
  } else if (hasProp(PR_ESSENTIALLY_GROUND)) {
    dropProp(PR_ESSENTIALLY_GROUND);
  }

  if ((_maxFunArity == 0) && onlyExistsForallPrefix(units)) {
    addProp(PR_ESSENTIALLY_BSR);
  }

  // information about sorts is read from the environment, not from the problem
  if (env.signature->hasSorts()) {
    addProp(PR_SORTS);
  }

  // information about interpreted constant is read from the signature
  if (env.signature->strings()) {
    addProp(PR_HAS_STRINGS);
  }
  if (env.signature->integers()) {
    addProp(PR_HAS_INTEGERS);
  }
  if (env.signature->rationals()) {
    addProp(PR_HAS_RATS);
  }
  if (env.signature->reals()) {
    addProp(PR_HAS_REALS);
  }


  // determine the category after adding
  if (formulas() > 0) { // FOF, either FEQ or FNE
    if (_equalityAtoms == 0) {
      _category = FNE;
    }
    else {
      _category = FEQ;
    }
  }
  // no formulas in the input, one of NEQ, HEQ, PEQ, HNE, NNE, EPR, UEQ
  else if (_maxFunArity == 0) { // all function symbols are constants
    if (_pureEquationalClauses == clauses()) { // only equations, UEQ or PEQ
      if (clauses() == unitClauses()) { // all clauses are unit
	_category = UEQ;
      }
      else {
	_category = PEQ;
      }
    }
    else {
      _category = EPR;
    }
  }
  // one of NEQ, HEQ, PEQ, HNE, NNE, UEQ
  else if (_equationalClauses == 0 ) { // HNE, NNE
    if (clauses() == hornClauses()) { // all clauses are horn
      _category = HNE;
    }
    else {
      _category = NNE;
    }
  }
  // one of NEQ, HEQ, PEQ, UEQ
  else if (_pureEquationalClauses == clauses()) { // only equations, UEQ or PEQ
    if (clauses() == unitClauses()) { // all clauses are unit
      _category = UEQ;
    }
    else {
      _category = PEQ;
    }
  }
  // one of NEQ, HEQ
  else if (clauses() == hornClauses()) { // all clauses are horn
    _category = HEQ;
  }
  else {
    _category = NEQ;
  }
} // Property::add(const UnitList* units)

/**
 * Scan property from a unit.
 *
 * @since 29/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types,
 *        formula scanning added
 * @since 26/05/2007 Manchester, changed to use new datastructures
 */
void Property::scan(Unit* unit)
{
  _symbolsInFormula.reset();

  if (unit->isClause()) {
    scan(static_cast<Clause*>(unit));
  }
  else {
    scan(static_cast<FormulaUnit*>(unit));
  }
  if (! hasProp(PR_HAS_FUNCTION_DEFINITIONS)) {
    FunctionDefinition::Def* def =
      FunctionDefinition::isFunctionDefinition(*unit,/*in the old, first-order sense*/false);
    if (def) {
      addProp(PR_HAS_FUNCTION_DEFINITIONS);
      FunctionDefinition::deleteDef(def);
    }
  }

  DHSet<int>::Iterator it(_symbolsInFormula);
  while(it.hasNext()){
    int symbol = it.next();
    if(symbol >= 0){
      env.signature->getFunction(symbol)->incUnitUsageCnt();
    }else{
      symbol = -symbol;
      env.signature->getPredicate(symbol)->incUnitUsageCnt();
    }
  }

} // Property::scan(const Unit* unit)

/**
 * Scan a clause.
 *
 * @param clause the clause
 * @since 29/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types
 * @since 27/08/2003 Vienna, changed to count variables
 * @since 26/05/2007 Manchester, changed to use new datastructures
 */
void Property::scan(Clause* clause)
{
  int positiveLiterals = 0;
  int negativeLiterals = 0;
  int equationalLiterals = 0;
  int positiveEquationalLiterals = 0;
  int groundLiterals = 0;
  _variablesInThisClause = 0;

  for (int i = clause->length()-1;i >= 0;i--) {
    Literal* literal = (*clause)[i];
    if (literal->isPositive()) {
      positiveLiterals ++;
    }
    else {
      negativeLiterals ++;
    }

    if (literal->isEquality()) {
      equationalLiterals++;
      if (literal->isPositive()) {
	positiveEquationalLiterals++;
      }
    }

    bool goal = (clause->inputType()==UnitInputType::CONJECTURE ||
        clause->inputType()==UnitInputType::NEGATED_CONJECTURE);
    bool unit = (clause->length() == 1);

    // 1 for context polarity, only used in formulas
    scan(literal,1,clause->length(),goal);

    SubtermIterator stit(literal);
    while (stit.hasNext()) {
      scan(stit.next(),unit,goal);
    }

    if (literal->shared() && literal->ground()) {
      groundLiterals++;
    }
  }
  int literals = positiveLiterals + negativeLiterals;
  _atoms += literals;

  if ( equationalLiterals > 0 ) {
    _equationalClauses ++;
    _equalityAtoms += equationalLiterals;
    _positiveEqualityAtoms += positiveEquationalLiterals;
  }
  if ( literals == equationalLiterals ) {
    _pureEquationalClauses ++;
  }

  if (clause->inputType() == UnitInputType::AXIOM) {
    _axiomClauses ++;
    if ( literals == 1) {
      _unitAxioms ++;
      if ( groundLiterals == 1) {
	_groundUnitAxioms ++;
      }
    }
    if (positiveLiterals <= 1) {
      _hornAxioms ++;
    }
    if (negativeLiterals == 0) {
      _positiveAxioms ++;
      if (literals == groundLiterals) {
	_groundPositiveAxioms ++;
      }
    }
  }
  else {
    _goalClauses ++;
    if ( literals == 1) {
      _unitGoals ++;
    }
    if (positiveLiterals <= 1) {
      _hornGoals ++;
    }
    if (literals == groundLiterals) {
      _groundGoals ++;
    }
  }

  _totalNumberOfVariables += _variablesInThisClause;
  if (_variablesInThisClause > _maxVariablesInClause) {
    _maxVariablesInClause = _variablesInThisClause;
  }
  if (! hasProp(PR_HAS_X_EQUALS_Y) && hasXEqualsY(clause)) {
    addProp(PR_HAS_X_EQUALS_Y);
  }

  if (_variablesInThisClause > 0) {
    _allClausesGround = false;
    if(!clause->isTheoryAxiom()){
      _allNonTheoryClausesGround = false;
    }
  }
} // Property::scan (const Clause* clause, bool isAxiom)


/**
 * Scan a formula unit.
 * @since 27/05/2007 flight Manchester-Frankfurt
 * @since 15/01/2014 Manchester, changed to use new hasXEqualsY
 * @author Andrei Voronkov
 */
void Property::scan(FormulaUnit* unit)
{
  if (unit->inputType() == UnitInputType::AXIOM) {
    _axiomFormulas ++;
  }
  else {
    _goalFormulas++;
  }
  Formula* f = unit->formula();

  SubexpressionIterator sei(f);
  while (sei.hasNext()) {
    SubexpressionIterator::Expression expr = sei.next();
    int polarity = expr.getPolarity();

    if (expr.isFormula()) {
      scan(expr.getFormula(), polarity);
    } else if (expr.isTerm()) {
      scan(expr.getTerm(),false,false); // only care about unit/goal when clausified
    } else {
      ASSERTION_VIOLATION;
    }
  }

  if (! hasProp(PR_HAS_X_EQUALS_Y)) {
    if (hasXEqualsY(f)) {
      addProp(PR_HAS_X_EQUALS_Y);
    }
  }
} // Property::scan


/**
 * Scan a formula.
 *
 * @since 17/07/2003 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
void Property::scan(Formula* f, int polarity)
{
  _subformulas++;
  switch(f->connective()) {
    case LITERAL: {
      _atoms++;
      Literal* lit = f->literal();
      if (lit->isEquality()) {
        _equalityAtoms++;
        if ((lit->isPositive() && polarity == 1) ||
            (!lit->isPositive() && polarity == -1) ||
            polarity == 0) {
          _positiveEqualityAtoms++;
        }
      }
      scan(lit,polarity,0,false); // 0 as not in clause, goal type irrelevant
      break;
    }
    case BOOL_TERM: {
      _hasFOOL = true;
      TermList ts = f->getBooleanTerm();
      if (ts.isVar()) {
        addProp(PR_HAS_BOOLEAN_VARIABLES);
      }
      break;
    }
    case FORALL:
      if(!_quantifiesOverPolymorphicVar){
        SList* sorts = f->sorts();
        SList::Iterator sit(sorts);

        while(sit.hasNext()){
          TermList s = sit.next();
          if(s.isTerm() && s.term()->isSuper()){
            _quantifiesOverPolymorphicVar = true;
            break;
          }
        }
      }
      if (polarity != -1) {
        _allQuantifiersEssentiallyExistential = false;
      }
      break;
    case EXISTS:
      if(!_quantifiesOverPolymorphicVar){
        SList* sorts = f->sorts();
        SList::Iterator sit(sorts);

        while(sit.hasNext()){
          TermList s = sit.next();
          if(s.isTerm() && s.term()->isSuper()){
            _quantifiesOverPolymorphicVar = true;
            break;
          }
        }
      }
      if (polarity != 1) {
        _allQuantifiersEssentiallyExistential = false;
      }
      break;
    default:
      break;
  }
} // Property::scan(const Formula&)

/**
 * If the sort is recognised by the properties, add information about it to the properties.
 * @since 04/05/2013 Manchester, array sorts removed
 * @author Andrei Voronkov
 */
void Property::scanSort(TermList sort)
{
  if(sort.isVar()){
    _hasNonDefaultSorts = true;
    return;
  }

  if(sort.term()->isSuper()){
    return;
  }

  if(sort.isArrowSort()){
    _hasArrowSort = true;
  }

  if(!higherOrder() && !hasPolymorphicSym()){
    //used sorts is for FMB which is not compatible with
    //higher-order or polymorphism
    unsigned sortU = sort.term()->functor();
    if(!_usesSort.get(sortU)){
      _sortsUsed++;
      _usesSort[sortU]=true;
    }
  }

  if (sort==AtomicSort::defaultSort()) {
    return;
  }
  _hasNonDefaultSorts = true;
  
  if(sort.isArraySort()){
    // an array sort is infinite, if the index or value sort is infinite
    // we rely on the recursive calls setting appropriate flags
    TermList idx = *sort.term()->nthArgument(0);
    scanSort(idx);
    TermList inner = *sort.term()->nthArgument(1);
    scanSort(inner);

    addProp(PR_HAS_ARRAYS);
    return;
  }
  if (env.signature->isTermAlgebraSort(sort)) {
    TermAlgebra* ta = env.signature->getTermAlgebraOfSort(sort);
    if (!ta->finiteDomain()) {
      _onlyFiniteDomainDatatypes = false;
    }
    if (ta->infiniteDomain()) {
      _knownInfiniteDomain = true;
    }
    if (ta->allowsCyclicTerms()) {
      addProp(PR_HAS_CDT_CONSTRUCTORS); // co-algebraic data type
    } else {
      addProp(PR_HAS_DT_CONSTRUCTORS); // algebraic data type
    }
    return;
  }

  if(HOL::finalResult(sort).isBoolSort()){
    _hasFOOL = true;
  }

  if(sort == AtomicSort::intSort()){
    addProp(PR_HAS_INTEGERS);
  } else
  if(sort == AtomicSort::rationalSort()){
    addProp(PR_HAS_RATS);
  } else
  if (sort == AtomicSort::realSort()){
    addProp(PR_HAS_REALS);
  } else 
  if (sort == AtomicSort::boolSort()){
    addProp(PR_HAS_BOOLEAN_VARIABLES);    
  }
}

/**
 * Scan a literal.
 *
 * @param lit the literal
 * @param polarity
 * @param cLen
 * @param goal
 * @since 29/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types
 * @since 27/05/2007 flight Manchester-Frankfurt, uses new datastructures
 */
void Property::scan(Literal* lit, int polarity, unsigned cLen, bool goal)
{
  if (lit->isEquality()) {
    TermList eqSort = SortHelper::getEqualityArgumentSort(lit);
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    if((lhs.isVar() || rhs.isVar()) && eqSort == AtomicSort::boolSort()){
      _hasBoolVar = true;
    }
    if((eqSort.isVar() || eqSort.term()->arity()) && 
       !eqSort.isArrowSort() && !eqSort.isArraySort() && !eqSort.isTupleSort()){
      _hasPolymorphicSym = true;      
    } 
    scanSort(eqSort);
  }
  else {
    _symbolsInFormula.insert(-lit->functor());
    int arity = lit->arity();
    if (arity > _maxPredArity) {
      _maxPredArity = arity;
    }
    Signature::Symbol* pred = env.signature->getPredicate(lit->functor());
    static bool weighted = env.options->symbolPrecedence() == Options::SymbolPrecedence::WEIGHTED_FREQUENCY ||
                           env.options->symbolPrecedence() == Options::SymbolPrecedence::REVERSE_WEIGHTED_FREQUENCY;
    unsigned w = weighted ? cLen : 1; 
    for(unsigned i=0;i<w;i++){pred->incUsageCnt();} //MS: Giles, was this a joke?
    if(cLen==1){
      pred->markInUnit();
    }
    if(goal){
      pred->markInGoal();
    }

    OperatorType* type = pred->predType();
    if(type->numTypeArguments()){
      _hasPolymorphicSym = true;
    }

    if (lit->isAnswerLiteral()) {
      _hasAnswerLiteral = true;
    }


    for (int i=0; i<arity; i++) {
      scanSort(SortHelper::getArgSort(lit, i));
    }
  }

 scanForInterpreted(lit);

  if (!hasProp(PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION) && lit->isEquality() && lit->shared()
     && ((lit->isNegative() && polarity == 1) || (!lit->isNegative() && polarity == -1) || polarity == 0)
     && !lit->ground() &&
     ( ( lit->nthArgument(0)->isVar() &&
	 !lit->nthArgument(1)->containsSubterm(*lit->nthArgument(0)) ) ||
       ( lit->nthArgument(1)->isVar() &&
	 !lit->nthArgument(0)->containsSubterm(*lit->nthArgument(1)) ))) {
    addProp(PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION);
  }
} // Property::scan(Literal* lit)


/**
 * Scan a term arguments.
 *
 * @param ts the list of terms
 * @param unit
 * @param goal
 * @since 29/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types,
 *        also NUMERIC case added
 * @since 27/08/2003 Vienna, changed to count variables
 * @since 27/05/2007 flight Manchester-Frankfurt, changed to new datastructures
 */
void Property::scan(TermList ts,bool unit,bool goal)
{
  if (ts.isVar()) {
    _variablesInThisClause++;
    return;
  }

  ASS(ts.isTerm());
  Term* t = ts.term();

  if (t->isSpecial()) {
    switch(t->specialFunctor()) {
      case SpecialFunctor::ITE:
        _hasFOOL = true;
        addProp(PR_HAS_ITE);
        break;

      case SpecialFunctor::LET:
        _hasFOOL = true;
        addProp(PR_HAS_LET_IN);
        break;
      case SpecialFunctor::FORMULA:
        _hasFOOL = true;
        break;

      case SpecialFunctor::MATCH:
        _hasFOOL = true;
        break;

      case SpecialFunctor::LAMBDA:
        _hasLambda = true;
        break;

    }
  } else {
    if(t->isSort()){
      if(t->arity() > _maxTypeConArity){
        _maxTypeConArity = t->arity();
      }
      return;
    }

    scanForInterpreted(t);

    _symbolsInFormula.insert(t->functor());
    Signature::Symbol* func = env.signature->getFunction(t->functor());
    func->incUsageCnt();
    if(unit){ func->markInUnit();}
    if(goal){ func->markInGoal();}

    if(t->isApplication()){
      _hasApp = true;
      TermList sort = SortHelper::getResultSort(t);
      if(HOL::finalResult(sort).isBoolSort() && ts.head().isVar()){
        _hasBoolVar = true;
      }
    }

    if(func->proxy() != Proxy::NOT_PROXY){
      if(func->proxy() == Proxy::PI || func->proxy() == Proxy::SIGMA) {
        ASS(t->arity() == 1);
        TermList sort = *t->nthArgument(0);
        if(HOL::finalResult(sort).isBoolSort()){
          _hasBoolVar = true;
        }
      }
      _hasLogicalProxy = true;
    }

    if(!t->isApplication() && t->numTypeArguments() > 0){
      _hasPolymorphicSym = true;
    }

    int arity = t->arity();

    if (arity > _maxFunArity) {
      _maxFunArity = arity;
    }

    for (int i = 0; i < arity; i++) {
      scanSort(SortHelper::getArgSort(t, i));
    }
    scanSort(SortHelper::getResultSort(t));  
  }
}

struct Setter {
  static void setNonLinear(Property& p,  IntTraits) { p._nonLinearInt  = true; }
  static void setNonLinear(Property& p,  RatTraits) { p._nonLinearRat  = true; }
  static void setNonLinear(Property& p, RealTraits) { p._nonLinearReal = true; }
  static void setHasNumerals(Property& p,  IntTraits) { p._hasNumeralsInt  = true; }
  static void setHasNumerals(Property& p,  RatTraits) { p._hasNumeralsRat  = true; }
  static void setHasNumerals(Property& p, RealTraits) { p._hasNumeralsReal = true; }
};

void Property::scanForInterpreted(Term* t)
{
  Interpretation itp;
  auto isNumeral = [&](auto n, auto t) { return t.isTerm() && !t.term()->isSpecial() && n.isNumeral(t.term()); };
  if (t->isLiteral()) {
    Literal* lit = static_cast<Literal*>(t);
    if (!theory->isInterpretedPredicate(lit->functor())) { return; }
    if (lit->isEquality()) {
      //cout << "this is interpreted equality " << t->toString() << endl;
      return; 
    }
    itp = theory->interpretPredicate(lit);
  }
  else {
    if (!theory->isInterpretedFunction(t)) { return; }
    itp = theory->interpretFunction(t);
    forEachNumTraits([&](auto n) {
      n.ifMul(t,[&](auto l, auto r) { 
        if (!isNumeral(n, l) && !isNumeral(n, r)) {
          Setter::setNonLinear(*this, n);
        }
        return std::make_tuple();
      });
    });
  }

  forEachNumTraits([&](auto n) {
    switch (t->kind()) {
      case TermKind::LITERAL:
      case TermKind::SORT:
        break;
      case TermKind::TERM:
        if (!t->isSpecial())
          n.ifNumeral(t, [&](auto) { Setter::setHasNumerals(*this, n); return std::make_tuple(); });
        break;
    }
  });
  _hasInterpreted = true;

  if(itp < _interpretationPresence.size()){
    _interpretationPresence[itp] = true;
  }

  if(Theory::isConversionOperation(itp)){
    addProp(PR_NUMBER_CONVERSION);
    return;
  }

  if (Theory::isPolymorphic(itp)) {
    OperatorType* type = t->isLiteral() ?
        env.signature->getPredicate(t->functor())->predType() : env.signature->getFunction(t->functor())->fnType();

    _polymorphicInterpretations.insert(std::make_pair(itp,type));
    return;
  }

  TermList sort = Theory::getOperationSort(itp);
  if(Theory::isInequality(itp)){
    if(sort == AtomicSort::intSort()){ addProp(PR_INTEGER_COMPARISON); }
    else if(sort == AtomicSort::rationalSort()){ addProp(PR_RAT_COMPARISON); }
    else if(sort == AtomicSort::realSort()){ addProp(PR_REAL_COMPARISON); }
  }
  else if(Theory::isLinearOperation(itp)){
    if(sort == AtomicSort::intSort()){ addProp(PR_INTEGER_LINEAR); }
    else if(sort == AtomicSort::rationalSort()){ addProp(PR_RAT_LINEAR); }
    else if(sort == AtomicSort::realSort()){ addProp(PR_REAL_LINEAR); }
  }
  else if(Theory::isNonLinearOperation(itp)){
    if(sort == AtomicSort::intSort()){ addProp(PR_INTEGER_NONLINEAR); }
    else if(sort == AtomicSort::rationalSort()){ addProp(PR_RAT_NONLINEAR); }
    else if(sort == AtomicSort::realSort()){ addProp(PR_REAL_NONLINEAR); }
  }
}

/**
 * Return the string representation of the CASC category.
 */
std::string Property::categoryString() const
{
  return categoryToString(_category);
}
std::string Property::categoryToString(Category cat)
{
  switch (cat)
    {
    case NEQ:
      return "NEQ";
    case HEQ:
      return "HEQ";
    case PEQ:
      return "PEQ";
    case HNE:
      return "HNE";
    case NNE:
      return "NNE";
    case FEQ:
      return "FEQ";
    case FNE:
      return "FNE";
    case EPR:
      return "EPR";
    case UEQ:
      return "UEQ";
    default:
      ASSERTION_VIOLATION;
    }
} // categoryString


/**
 * Output the property to a string readable by a human. NOT ALL FIELDS
 * ARE CURRENTLY OUTPUT.
 * @since 27/08/2003 Vienna
 */
std::string Property::toString() const
{
  std::string result("TPTP class: ");
  result += categoryString() + "\n";

  if (clauses() > 0) {
    result += "Clauses: ";
    result += Int::toString(clauses());
    result += " (";
    result += Int::toString(_unitAxioms+_unitGoals);
    result += " unit, ";
    result += Int::toString(_goalClauses);
    result += " goal, ";
    result += Int::toString(_equationalClauses);
    result += " equational)\n";

    result += "Variables: ";
    result += Int::toString(_totalNumberOfVariables);
    result += " (";
    result += Int::toString(_maxVariablesInClause);
    result += " maximum in a single clause)\n";
  }

  if (formulas() > 0) {
    result += "Formulas: ";
    result += Int::toString(formulas());
    result += " (";
    result += Int::toString(_goalFormulas);
    result += " goal)\n";
    result += "Subformulas: ";
    result += Int::toString(_subformulas);
    result += "\n";
  }

  result += "Atoms: ";
  result += Int::toString(_atoms);
  result += " (";
  result += Int::toString(_equalityAtoms);
  result += " equality)\n";

  return result;
} // Property::toString


/**
 * True if the clause contains a positive literal X=Y.
 * @since 04/06/2004 Manchester
 * @since 27/05/2007 Frankfurt airport, changed to new datastructures
 * @since 15/01/2014 Manchester, reimplemented
 * @author Andrei Voronkov
 */
bool Property::hasXEqualsY(const Clause* c)
{
  for (int i = c->length()-1; i >= 0; i--) {
    const Literal* lit = (*c)[i];
    if (lit->isNegative()) {
      continue;
    }
    if (!lit->isEquality()) {
      continue;
    }
    const TermList* ts1 = lit->args();
    if (!ts1->isVar()) {
      continue;
    }
    const TermList* ts2 = ts1->next();
    if (ts2->isVar() &&
      ts1->var() != ts2->var()) {
      return true;
    }
  }
  return false;
} // Property::hasXEqualsY(const Clause*)

/**
 * True if the subformula formula would have a literal X=Y
 * after clausification.
 *
 * @param f the formula
 * @since 11/12/2004 Manchester, true and false added
 * @since 27/05/2007 flight Frankfurt-Lisbon, changed to new datastructures
 * @since 15/01/2014 Manchester, bug fix and improvement
 * @author Andrei Voronkov
 * @warning this function can be improved, but at a higher cost, it also does not treat let constructs
 *          and if-then-else terms
 */
bool Property::hasXEqualsY(const Formula* f)
{
  ZIArray<bool> existVars; // "in the currently processed subformula, marks variables which will clausify only as existential"

  struct Rec {
    bool cleanup;
    union {
      struct {
        const Formula* form;
        int pol;
      } FlaRec;
      struct {
        unsigned var;
        bool origVal;
      } VarRec;
    };

    Rec(const Formula* f, int p)
      : cleanup(false), FlaRec{f, p} {}

    Rec(unsigned v, bool val)
      : cleanup(true), VarRec{v,val} {}
  };
  Stack<Rec> recs;

  recs.push(Rec(f,1));

  while (!recs.isEmpty()) {
    auto rec = recs.pop();

    if (rec.cleanup) {
      existVars[rec.VarRec.var] = rec.VarRec.origVal;
      continue;
    }
    auto [f,pol] = rec.FlaRec;
    int eff_pol = pol; // unless changed in the EXISTS case below

    switch (f->connective()) {
    case LITERAL:
      {
        const Literal* lit = f->literal();

        if (!lit->isEquality()) {
          break;
        }
        const TermList* ts1 = lit->args();
        if (!ts1->isVar()) {
          break;
        }
        const TermList* ts2 = ts1->next();
        if (!ts2->isVar()) {
          break;
        }
        unsigned v1 = ts1->var();
        unsigned v2 = ts2->var();
        if (v1 == v2) {
          break;
        }
        if (!lit->isPositive()) {
          pol = -pol;
        }
        if (pol >= 0 && !existVars.get(v1) && !existVars.get(v2)) {
          return true;
        }
      }
      break;

    case AND:
    case OR:
      {
        FormulaList::Iterator fs(f->args());
        while (fs.hasNext()) {
          recs.push(Rec(fs.next(),pol));
        }
      }
      break;

    case IMP:
      recs.push(Rec(f->left(),-pol));
      recs.push(Rec(f->right(),pol));
      break;

    case IFF:
    case XOR:
      recs.push(Rec(f->left(),0));
      recs.push(Rec(f->right(),0));
      break;

    case NOT:
      recs.push(Rec(f->uarg(),-pol));
      break;

    case EXISTS:
      eff_pol = -pol;
    case FORALL:
      if (eff_pol >= 0) {
        // will have a universal version
        VList::Iterator vs(f->vars());
        while (vs.hasNext()) {
          unsigned v = vs.next();
          if (existVars[v]) {
            existVars[v] = false;
            recs.push(Rec(v,true)); // restore back to true
          }
        }
      } else {
        // only existential
        VList::Iterator vs(f->vars());
        while (vs.hasNext()) {
          unsigned v = vs.next();
          if (!existVars[v]) {
            existVars[v] = true;
            recs.push(Rec(v,false)); // restore back to false
          }
        }
      }
      recs.push(Rec(f->qarg(),pol));
      break;

    case TRUE:
    case FALSE:
      break;

    case BOOL_TERM:
      return true; // MS: Aztek, why this?

    case NAME:
    case NOCONN:
      ASSERTION_VIOLATION;
    }
  }
  return false;
} // Property::hasXEqualsY(const Formula* f)


/**
 * True if f should clausify to only introduce constants as Skolems.
 *
 * @warning Works correctly only closed formulas!
 */
bool Property::onlyExistsForallPrefix(UnitList* units)
{
  struct Rec {
    const Formula* form;
    int pol; // polarities
    int state; // states: no commitment yet (0) - exists block (1) - forall block (2) - bailout (returns false)
  };
  Stack<Rec> recs;

  UnitList::Iterator us(units);
  while (us.hasNext()) {
    Unit* unit = us.next();
    if (unit->isClause()) continue;
    const Formula* f = static_cast<FormulaUnit*>(unit)->formula();

    recs.push({f,1,0});

    while (!recs.isEmpty()) {
      auto [f,pol,state] = recs.pop();
      int eff_pol = pol; // unless changed in the EXISTS case below

      switch (f->connective()) {
      case LITERAL:
        // we are good with this one
        break;

      case AND:
      case OR:
        {
          FormulaList::Iterator fs(f->args());
          while (fs.hasNext()) {
            recs.push({fs.next(),pol,state});
          }
        }
        break;

      case IMP:
        recs.push({f->left(),-pol,state});
        recs.push({f->right(),pol,state});
        break;

      case IFF:
      case XOR:
        recs.push({f->left(),0,state});
        recs.push({f->right(),0,state});
        break;

      case NOT:
        recs.push({f->uarg(),-pol,state});
        break;

      case EXISTS:
        eff_pol = -pol;
      case FORALL:
        if (eff_pol == 1) {
          recs.push({f->qarg(),pol,2}); // in the forall bit now
        } else if (eff_pol == -1) {
          if (state >= 2) { // exists below forall
            return false;
          }
          recs.push({f->qarg(),pol,1}); // in the exists bit now
        } else { // pol == 0
          if (state <= 1) { // we will do both polarities now, so, conservatibely, we are "already" in the forall part
            recs.push({f->qarg(),pol,2}); // in the forall bit now
          } else {
            return false;
          }
        }
        break;

      case TRUE:
      case FALSE:
        break;

      case BOOL_TERM:
        return false; // FOOL stuff is out

      case NAME:
      case NOCONN:
        ASSERTION_VIOLATION;
      }
    }
  }

  return true;
} // Property::onlyExistsForallPrefix(UnitList* units)


/**
 * Transforms the property to an SQL command asserting this
 * property to the Spider database. An example of a command is
 * "UPDATE problem SET property=0,category='NNE' WHERE name='TOP019-1';".
 *
 * @since 04/05/2005 Manchester
 */
std::string Property::toSpider(const std::string& problemName) const
{
  return (std::string)"UPDATE problem SET property="
    + Int::toString((int)_props)
    + ",category='"
    + categoryString()
    + "' WHERE name='"
    + problemName +
    + "';";
} // Property::toSpider

/**
 * Reflect the state of Property into a "python-style" representation
 * as a dictionary of key-valey (string) pairs. In particular,
 * Options::sampleStrategy is eagerly waiting for this to be able to do property-conditioned sampling.
 */
DHMap<std::string,std::string> Property::toDict() const
{
  DHMap<std::string,std::string> result;
  result.set("@hasFormulas",Int::toString(hasFormulas()));
  result.set("@hasEquality",Int::toString(equalityAtoms()>0));
  result.set("@hasFOOL",Int::toString(hasFOOL()));
  result.set("@hasGoal",Int::toString(hasGoal()));
  result.set("@essentiallyGround",Int::toString(hasProp(PR_ESSENTIALLY_GROUND)));
  result.set("@essentiallyBSR",Int::toString(hasProp(PR_ESSENTIALLY_BSR)));

  result.set("@cat",categoryString());
  for (unsigned i = 1, n = 2; i <= 25; i++, n *= 2){
    result.set("@atoms_leq_2^"+Int::toString(i),Int::toString((unsigned)atoms() <= n));
  }
  return result;
} // Property::toDict

} // namespace Shell
