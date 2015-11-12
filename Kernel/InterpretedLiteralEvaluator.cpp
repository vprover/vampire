/**
 * @file InterpretedLiteralEvaluator.cpp
 * Implements class InterpretedLiteralEvaluator.
 */

#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"

#include "InterpretedLiteralEvaluator.hpp"

namespace Kernel
{

/**
 * We use descendants of this class to evaluate various functions.
 *
 * One function can be evaluated only by one Evaluator object.
 */
class InterpretedLiteralEvaluator::Evaluator
{
public:
  CLASS_NAME(InterpretedLiteralEvaluator::Evaluator);
  USE_ALLOCATOR(InterpretedLiteralEvaluator::Evaluator);
  
  virtual ~Evaluator() {}

  bool canEvaluateFunc(unsigned func)
  {
    CALL("InterpretedLiteralEvaluator::Evaluator::canEvaluateFunc");

    if (!theory->isInterpretedFunction(func)) {
      return false;
    }
    Interpretation interp = theory->interpretFunction(func);
    return canEvaluate(interp);
  }

  bool canEvaluatePred(unsigned pred)
  {
    CALL("InterpretedLiteralEvaluator::Evaluator::canEvaluatePred");

    if (!theory->isInterpretedPredicate(pred)) {
      return false;
    }
    Interpretation interp = theory->interpretPredicate(pred);
    return canEvaluate(interp);
  }

  virtual bool canEvaluate(Interpretation interp) = 0;
  virtual bool tryEvaluateFunc(Term* trm, TermList& res) { return false; }
  virtual bool tryEvaluatePred(Literal* trm, bool& res)  { return false; }
};


/**
 * Interpreted equality has to be treated specially. We do not have separate
 * predicate symbols for different kinds of equality so the sorts must be 
 * detected and the correct intepretation of constants carried out.
 *
 * Equality is only decided between constant terms.
 *
 * @author Giles
 * @since 10/11/14
 */
class InterpretedLiteralEvaluator::EqualityEvaluator
  : public Evaluator
{

  virtual bool canEvaluate(Interpretation interp)
  {
    return interp==Interpretation::EQUAL; 
  }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res)
  {
    ASSERTION_VIOLATION; // EQUAL is a predicate, not a function!
  }

  template<typename T>
  bool checkEquality(Literal* lit, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::EqualityEvaluator::checkEquality");
    T arg1;
    if(!theory->tryInterpretConstant(lit->nthArgument(0)->term(),arg1)){ 
      return false; 
    }
    T arg2;
    if(!theory->tryInterpretConstant(lit->nthArgument(1)->term(),arg2)){ 
      return false;
    }

    res = (arg1 == arg2);

    return true;
  }

  bool tryEvaluatePred(Literal* lit, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::EqualityEvaluator::tryEvaluatePred");

    try{

      Interpretation itp = theory->interpretPredicate(lit);
      ASS(itp==Interpretation::EQUAL);
      ASS(theory->getArity(itp)==2);
    
      // We try and interpret the equality as a number of different sorts
      // If it is not an equality between two constants of the same sort the
      // checkEquality function will return false, otherwise res will contain
      // the result of the equality check
      bool okay = checkEquality<IntegerConstantType>(lit,res)  ||
                  checkEquality<RationalConstantType>(lit,res) ||
                  checkEquality<RealConstantType>(lit,res);

      if(!okay) return false;

      if(lit->isNegative()){ res = !res; }

      return true;

    }
    catch(ArithmeticException&)
    {
      return false;
    }

  }

};

/**
 * An evaluator for dealing with conversions between sorts
 *
 */
class InterpretedLiteralEvaluator::ConversionEvaluator
  : public Evaluator
{
public:
  virtual bool canEvaluate(Interpretation interp)
  {
    CALL("InterpretedLiteralEvaluator::ConversionEvaluator::canEvaluate");
    return theory->isConversionOperation(interp);
  }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res)
  {
    CALL("InterpretedLiteralEvaluator::ConversionEvaluator::tryEvaluateFunc");
    ASS(theory->isInterpretedFunction(trm));

    try {
      Interpretation itp = theory->interpretFunction(trm);
      ASS(theory->isFunction(itp));
      ASS(theory->isConversionOperation(itp));
      ASS_EQ(theory->getArity(itp), 1);

      TermList argTrm = *trm->nthArgument(0);
      switch(itp) {
      case Theory::INT_TO_RAT:
	{
	  IntegerConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) { 
	    return false;
	  }
	  RationalConstantType resNum(arg,1);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::INT_TO_REAL:
	{
	  IntegerConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RealConstantType resNum(RationalConstantType(arg,1));
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::RAT_TO_INT:
	{
	  RationalConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  IntegerConstantType resNum = IntegerConstantType::floor(arg);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::RAT_TO_REAL:
	{
	  RationalConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RealConstantType resNum(arg);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::REAL_TO_INT:
	{
	  RealConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  IntegerConstantType resNum = IntegerConstantType::floor(RationalConstantType(arg));
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::REAL_TO_RAT:
	{
	  //this is correct only as long as we only represent rational real numbers
	  RealConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RationalConstantType resNum(arg);
	  res = TermList(theory->representConstant(resNum));
	return true;
      }

      default:
	ASSERTION_VIOLATION;
      }
    }
    catch(ArithmeticException&)
    {
      return false;
    }
  }
};

/**
 * Evaluates constant theory expressions
 *
 * Evaluators for each sort implement tryEvaluate(Unary/Binary)(Func/Pred) 
 * 
 */
template<class T>
class InterpretedLiteralEvaluator::TypedEvaluator : public Evaluator
{
public:
  typedef T Value;

  TypedEvaluator() {}

  virtual bool isOne(T arg) = 0;
  virtual bool isDivision(Interpretation interp) = 0;

  virtual bool canEvaluate(Interpretation interp)
  {
    CALL("InterpretedLiteralEvaluator::TypedEvaluator::canEvaluate");

    //only interpreted operations with non-single argument sort are array operations
    if (theory->isArrayOperation(interp))
    {
        unsigned opSort = theory->getArrayOperationSort(interp);
        return opSort==T::getSort();
    }
    
    // This is why we cannot evaluate Equality here... we cannot determine its sort
    if (!theory->hasSingleSort(interp)) { return false; } //To skip conversions and EQUAL

    unsigned opSort = theory->getOperationSort(interp);
    return opSort==T::getSort();
  }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res)
  {
    CALL("InterpretedLiteralEvaluator::tryEvaluateFunc");
    ASS(theory->isInterpretedFunction(trm));

    //cout << "try evaluate " << trm->toString() << endl;

    try {
      Interpretation itp = theory->interpretFunction(trm);
      ASS(theory->isFunction(itp));
      unsigned arity = theory->getArity(itp);

      if (arity!=1 && arity!=2) {
	INVALID_OPERATION("unsupported arity of interpreted operation: "+Int::toString(arity));
      }
      T resNum;
      TermList arg1Trm = *trm->nthArgument(0);
      T arg1;
      if (!theory->tryInterpretConstant(arg1Trm, arg1)) { 
        //Special case where itp is division and arg2 is '1'
        T arg2;
        if(arity==2 && theory->tryInterpretConstant(*trm->nthArgument(1),arg2) 
                    && isOne(arg2) && isDivision(itp)){
          res = arg1Trm;
          return true;
        }
        return false; 
      }
      if (arity==1) {
	if (!tryEvaluateUnaryFunc(itp, arg1, resNum)) { return false;}
      }
      else if (arity==2) {
	TermList arg2Trm = *trm->nthArgument(1);
	T arg2;
	if (!theory->tryInterpretConstant(arg2Trm, arg2)) { return false; }
	if (!tryEvaluateBinaryFunc(itp, arg1, arg2, resNum)) { return false;}
      }
      res = TermList(theory->representConstant(resNum));
      return true;
    }
    catch(ArithmeticException)
    {
       //cout << "ArithmeticException" << endl;
      return false;
    }
  }

  virtual bool tryEvaluatePred(Literal* lit, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::tryEvaluatePred");
    ASS(theory->isInterpretedPredicate(lit));

    try {
      Interpretation itp = theory->interpretPredicate(lit);
      ASS(!theory->isFunction(itp));
      unsigned arity = theory->getArity(itp);

      if (arity!=1 && arity!=2) {
	INVALID_OPERATION("unsupported arity of interpreted operation: "+Int::toString(arity));
      }
      TermList arg1Trm = *lit->nthArgument(0);
      T arg1;
      if (!theory->tryInterpretConstant(arg1Trm, arg1)) { return false; }
      if (arity==1) {
	if (!tryEvaluateUnaryPred(itp, arg1, res)) { return false;}
      }
      else {
	TermList arg2Trm = *lit->nthArgument(1);
	T arg2;
	if (!theory->tryInterpretConstant(arg2Trm, arg2)) { return false; }
	if (!tryEvaluateBinaryPred(itp, arg1, arg2, res)) { return false;}
      }
      if (lit->isNegative()) {
	res = !res;
      }
      return true;
    }
    catch(ArithmeticException&)
    {
      return false;
    }

  }
protected:
  virtual bool tryEvaluateUnaryFunc(Interpretation op, const T& arg, T& res)
  { return false; }
  virtual bool tryEvaluateBinaryFunc(Interpretation op, const T& arg1, const T& arg2, T& res)
  { return false; }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const T& arg1, bool& res)
  { return false; }
  virtual bool tryEvaluateBinaryPred(Interpretation op, const T& arg1, const T& arg2, bool& res)
  { return false; }
};

/**
 * Evaluates integer functions
 */
class InterpretedLiteralEvaluator::IntEvaluator : public TypedEvaluator<IntegerConstantType>
{
protected:

  virtual bool isOne(IntegerConstantType arg){ return arg.toInner()==1;}
  virtual bool isDivision(Interpretation interp){ return interp==Theory::INT_DIVIDE; }

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::INT_UNARY_MINUS:
      res = -arg;
      return true;
    case Theory::INT_ABS:
      if (arg < 0) {
        res = -arg;
      } else {
        res = arg;
      }
      return true;
    case Theory::INT_SUCCESSOR:
      res = arg+1;
      return true;
    case Theory::INT_FLOOR:
    case Theory::INT_CEILING:
    case Theory::INT_TRUNCATE:
    case Theory::INT_ROUND:
       // For integers these do nothing
      res = arg;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::INT_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::INT_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::INT_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::INT_DIVIDE:
      res = arg1/arg2;
      return true;
    case Theory::INT_MODULO:
      res = arg1%arg2;
      return true;
    case Theory::INT_QUOTIENT_E:
      res = arg1.quotientE(arg2);
      return true;
    case Theory::INT_QUOTIENT_T:
      res = arg1.quotientT(arg2);
      return true;
    case Theory::INT_QUOTIENT_F:
      res = arg1.quotientF(arg2);
      return true;
    // The remainder is left - (quotient * right)
    case Theory::INT_REMAINDER_E:
      res = arg1 - (arg1.quotientE(arg2)*arg2);
      return true;
    case Theory::INT_REMAINDER_T:
      res = arg1 - (arg1.quotientT(arg2)*arg2);
      return true;
    case Theory::INT_REMAINDER_F:
      res = arg1 - (arg1.quotientF(arg2)*arg2);
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::INT_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::INT_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::INT_LESS:
      res = arg1<arg2;
      return true;
    case Theory::INT_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    case Theory::INT_DIVIDES:
      res = (arg2%arg1)==0;
      return true;
    default:
      return false;
    }
  }
};

/**
 * Evaluations rational functions
 */
class InterpretedLiteralEvaluator::RatEvaluator : public TypedEvaluator<RationalConstantType>
{
protected:
  virtual bool isOne(RationalConstantType arg) { return arg.numerator()==arg.denominator();}
  virtual bool isDivision(Interpretation interp){ return interp==Theory::RAT_DIVIDE;}

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::RAT_UNARY_MINUS:
      res = -arg;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::RAT_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::RAT_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::RAT_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::RAT_DIVIDE:
      res = arg1/arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::RAT_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::RAT_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::RAT_LESS:
      res = arg1<arg2;
      return true;
    case Theory::RAT_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const Value& arg1,
      bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::RAT_IS_INT:
      res = arg1.isInt();
      return true;
    default:
      return false;
    }
  }
};

/**
 * Evaluates real functions. 
 * As reals are represented as rationals the operations are for reals.
 * See Kernel/Theory.hpp for how these operations are defined
 */
class InterpretedLiteralEvaluator::RealEvaluator : public TypedEvaluator<RealConstantType>
{
protected:
  virtual bool isOne(RealConstantType arg) { return arg.numerator()==arg.denominator();}
  virtual bool isDivision(Interpretation interp){ return interp==Theory::REAL_DIVIDE;}

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::REAL_UNARY_MINUS:
      res = -arg;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::REAL_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::REAL_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::REAL_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::REAL_DIVIDE:
      res = arg1/arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::REAL_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::REAL_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::REAL_LESS:
      res = arg1<arg2;
      return true;
    case Theory::REAL_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const Value& arg1,
      bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::REAL_IS_INT:
      res = arg1.isInt();
      return true;
    case Theory::REAL_IS_RAT:
      //this is true as long as we can evaluate only rational reals.
      res = true;
      return true;
    default:
      return false;
    }
  }

};

////////////////////////////////
// InterpretedLiteralEvaluator
//
// This is where the evaluators defined above are used.

InterpretedLiteralEvaluator::InterpretedLiteralEvaluator()
{
  CALL("InterpretedLiteralEvaluator::InterpretedLiteralEvaluator");

  // For an evaluator to be used it must be pushed onto _evals
  // We search this list, calling canEvaluate on each evaluator
  // An invariant we want to maintain is that for any literal only one
  //  Evaluator will return true for canEvaluate
  _evals.push(new IntEvaluator());
  _evals.push(new RatEvaluator());
  _evals.push(new RealEvaluator());
  _evals.push(new ConversionEvaluator());
  _evals.push(new EqualityEvaluator());

  _funEvaluators.ensure(0);
  _predEvaluators.ensure(0);

}

InterpretedLiteralEvaluator::~InterpretedLiteralEvaluator()
{
  CALL("InterpretedEvaluation::LiteralSimplifier::~LiteralSimplifier");

  while (_evals.isNonEmpty()) {
    delete _evals.pop();
  }
}

/**
 * This checks if a literal is 'balancable' i.e. can be put into the form term=constant or term=var
 * 
 * This is still an experimental process and will be expanded/reworked later
 *
 * @author Giles
 * @since 11/11/14
 */
bool InterpretedLiteralEvaluator::balancable(Literal* lit)
{
  CALL("InterpretedLiteralEvaluator::balancable");
  // Check that lit is compatible with this balancing operation
  // One thing that we cannot check, but assume is that it has already been simplified once
  // balance applies further checks

  // lit must be an interpretted predicate
  if(!theory->isInterpretedPredicate(lit->functor())) return false;

  // the perdicate must be binary
  Interpretation ip = theory->interpretPredicate(lit->functor());
  if(theory->getArity(ip)!=2) return false;

  // one side must be a constant and the other interpretted
  // the other side can contain at most one variable or uninterpreted subterm 
  // but we do not check this second condition here, instead we detect it in balance
  TermList t1 = *lit->nthArgument(0);
  TermList t2 = *lit->nthArgument(1);
  if(theory->isInterpretedConstant(t1)){
    if(theory->isInterpretedConstant(t2)) return false; // already balanced
    if(t2.isVar()) return false; // already balanced
    if(!theory->isInterpretedFunction(t2)) return false; // cannot balance
  }else if(theory->isInterpretedConstant(t2)){
    if(theory->isInterpretedConstant(t1)) return false; // already balanced
    if(t1.isVar()) return false;//already balanced
    if(!theory->isInterpretedFunction(t1)) return false; // cannot balance

  }else { return false; } // neither side constant

  return true;
}

/**
 * This attempts to 'balance' a literal i.e. put it into the form term=constant
 *
 * The current implementation is only applicable to a restricted set of cases.
 *
 * This is still an experimental process and will be expanded/reworked later
 *
 * @author Giles
 * @since 11/11/14
 */
bool InterpretedLiteralEvaluator::balance(Literal* lit,Literal*& resLit,Stack<Literal*>& sideConditions)
{
  CALL("InterpretedLiteralEvaluator::balance");
  ASS(balancable(lit));

  //cout << "try balance " << lit->toString() << endl;

  ASS(theory->isInterpretedPredicate(lit->functor()));

  // currently only works for equality!!
  // because I don't deal with inverting inequalities when dividing by negatives
  // TODO - extend this to inequalities
  if(theory->interpretPredicate(lit->functor())!=Interpretation::EQUAL) return false;

  //cout << "Attempting to balance " << lit->toString() << endl;

  TermList t1;
  TermList t2;
  // ensure that t1 is the constant
  if(theory->isInterpretedConstant(*lit->nthArgument(0))){
    t1 = *lit->nthArgument(0); t2 = *lit->nthArgument(1);
  }else{
    t1 = *lit->nthArgument(1); t2 = *lit->nthArgument(0);
  }

  // Implied by balancable
  //if(t2.isVar()){ return true;} //already balanced!
  //if(!theory->isInterpretedFunction(t2)){ return false;} // cannot start

  // Recurse over structure of t2, applying interpreted functions to t1
  // i.e. if we have t2=f(c,t4) and t1=d then we change pointers so that
  //    t2=t4 and t1=f^(d,c)
  // This relies on the fact that a simplified literal with a single non-constant
  // subterm will look like f(c,f(c,f(c,t)))=c
  // If we cannot invert an interpreted function f then we fail

  while(theory->isInterpretedFunction(t2)){
    //cout << "reducing " << t2.toString() << endl;
    //find non-constant argument
    TermList* args = t2.term()->args();
    
    TermList* non_constant=0;
    while(args->isNonEmpty()){
      if(!theory->isInterpretedConstant(*args)){
        if(non_constant){
          return false; // If there is more than one non-constant term this will not work
                        // TODO extend approach to this case 
        }
        non_constant=args;
      } 
      args= args->next();
    }
    //Should not happen if balancable passed and it was simplified
    if(!non_constant){ return false;} 
    
    //get function inverse, need information about parameter order
    //  i.e. inverse of multiply is divide where 
    //                multiply(x,_) and multiply(_,x) => divide(_,x) 
    // it is of the form (orig,non-con-arg,replacement) 
    // i.e. f(t,c1),t,c2 => f^(c1,c2) ... where f^ is f inverted and the ordering of its 
    //      args are decided in invertInterptedFunction
    TermList rep; 
    if(!theory->invertInterpretedFunction(t2.term(),non_constant,t1,rep,sideConditions)){
      // if no inverse then return false... cannot balance
      //cout << "Fail due to lack of inverse" << endl;
      return false;
    }

    // update t1
    t1=rep;
    // set t2 to the non-constant argument
    t2 = *non_constant;
  }

  //Evaluate t1
  // We have rearranged things so that t2 is a non-constant term and t1 is a number
  // of interprted functions applied to some constants. By evaluating t1 we will
  //  get a constant (unless evaluation is not possible)

  TermList new_args[] = {t1,t2}; 
  resLit = TermTransformer::transform(Literal::create(lit,new_args));
  return true;
}

/**
 * Used to evaluate a literal, setting isConstant, resLit and resConst in the process
 *
 * Returns true if it has been evaluated, in which case resLit is set 
 * isConstant is true if the literal predicate evaluates to a constant value
 * resConst is set iff isConstant and gives the constant value (true/false) of resLit 
 */
bool InterpretedLiteralEvaluator::evaluate(Literal* lit, bool& isConstant, Literal*& resLit, bool& resConst,Stack<Literal*>& sideConditions)
{
  CALL("InterpretedLiteralEvaluator::evaluate");

  //cout << "evaluate " << lit->toString() << endl;

  // This tries to transform each subterm using tryEvaluateFunc (see transform Subterm below)
  resLit = TermTransformer::transform(lit);

  //cout << "transformed " << resLit->toString() << endl;

  // If it can be balanced we balance it
  // A predicate on constants will not be balancable
  if(balancable(resLit)){
      Literal* new_resLit=resLit;
      bool balance_result = balance(resLit,new_resLit,sideConditions);
      ASS(balance_result || resLit==new_resLit);
      resLit=new_resLit;
  }

  // If resLit contains variables the predicate cannot be interpreted
  VariableIterator vit(lit);
  if(vit.hasNext()){
    isConstant=false;
    return (lit!=resLit);
  }
  //cout << lit->toString()<< " is variable free, evaluating..." << endl;

  unsigned pred = resLit->functor();

  // Now we try and evaluate the predicate
  Evaluator* predEv = getPredEvaluator(pred);
  if (predEv) {
    if (predEv->tryEvaluatePred(resLit, resConst)) {
        //cout << "pred evaluated " << resConst << endl;
	isConstant = true;
	return true;
    }
  }
  if (resLit!=lit) {
    isConstant = false;
    return true;
  }
  return false;
}

/**
 * This attempts to evaluate each subterm.
 * See Kernel/TermTransformer for how it is used.
 * Terms are evaluated bottom-up
 */
TermList InterpretedLiteralEvaluator::transformSubterm(TermList trm)
{
  CALL("InterpretedLiteralEvaluator::transformSubterm");

  if (!trm.isTerm()) { return trm; }
  Term* t = trm.term();
  unsigned func = t->functor();

  Evaluator* funcEv = getFuncEvaluator(func);
  if (funcEv) {
    TermList res;
    if (funcEv->tryEvaluateFunc(t, res)) {
	return res;
    }
  }
  return trm;
}

/**
 * This searches for an Evaluator for a function
 */
InterpretedLiteralEvaluator::Evaluator* InterpretedLiteralEvaluator::getFuncEvaluator(unsigned func)
{
  CALL("InterpretedLiteralEvaluator::getFuncEvaluator");

  if (func>=_funEvaluators.size()) {
    unsigned oldSz = _funEvaluators.size();
    unsigned newSz = func+1;
    _funEvaluators.expand(newSz);
    for (unsigned i=oldSz; i<newSz; i++) {
	EvalStack::Iterator evit(_evals);
	while (evit.hasNext()) {
	  Evaluator* ev = evit.next();
	  if (ev->canEvaluateFunc(i)) {
	    ASS_EQ(_funEvaluators[i], 0); //we should have only one evaluator for each function
	    _funEvaluators[i] = ev;
	  }
	}
    }
  }
  return _funEvaluators[func];
}

/**
 * This searches for an Evaluator for a predicate
 */
InterpretedLiteralEvaluator::Evaluator* InterpretedLiteralEvaluator::getPredEvaluator(unsigned pred)
{
  CALL("InterpretedLiteralEvaluator::getPredEvaluator");

  if (pred>=_predEvaluators.size()) {
    unsigned oldSz = _predEvaluators.size();
    unsigned newSz = pred+1;
    _predEvaluators.expand(newSz);
    for (unsigned i=oldSz; i<newSz; i++) {
      EvalStack::Iterator evit(_evals);
      while (evit.hasNext()) {
	Evaluator* ev = evit.next();
	if (ev->canEvaluatePred(i)) {
	  ASS_EQ(_predEvaluators[i], 0); //we should have only one evaluator for each predicate
	  _predEvaluators[i] = ev;
	}
      }
    }
  }
  return _predEvaluators[pred];
}

}
