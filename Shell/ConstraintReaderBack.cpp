
/*
 * File ConstraintReaderBack.cpp.
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
 * @file ConstraintReaderBack.cpp
 * Implements ConstraintReader and related classes
 */
#if GNUMP

#include <fstream>
#include <iostream>

#include <Forwards.hpp>

#include "Lib/Environment.hpp"
#include "Lib/RCPtr.hpp"
#include "Shell/Options.hpp"
#include "Kernel/Number.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Connective.hpp"
#include "Lib/VString.hpp"

#include "SMTPAR.hpp"
#include "Parse/SMTLIB.hpp"
#include "Parse/SMTLIB2.hpp"
#include "ConstraintReaderBack.hpp"

using namespace Shell;
using namespace Kernel;
using namespace Parse;
using namespace std;

SMTLib2ConstraintReader::SMTLib2ConstraintReader(Parse::SMTLIB2& parser)
  :_sig(*env.signature), _parser(parser) {
  CALL("SMTLib2ConstraintReader::SMTLib2ConstraintReader(Parse::SMTLIB2)");
}

ConstraintRCList* SMTLib2ConstraintReader::constraints(){
  CALL("SMTLib2ConstraintReader::constraints()");
  ConstraintRCList* res=0;
  Stack<SMTLIB2::FunctionInfo> functions = _parser.getFuncInfos();

  //add functions to the signature
  for(unsigned index = 0; index < functions.size(); index++){
      SMTLIB2::FunctionInfo fnInfo = functions[index];
      _sig.addVar(fnInfo.name);
  }

  Formula* form = _parser.getFormula1();
  if(form->connective()!= Kernel::AND){
    USER_ERROR("and expected");
  }

  FormulaList* formList = form->args();
  FormulaList::Iterator itef(formList);
  //check if there exist other type of operation except &. If that is the case,
  //report an user error and terminate the program
  while(itef.hasNext())
    {
      Formula* f = itef.next();
      if(!(f->connective() == Kernel::AND || f->connective() == Kernel::LITERAL)){
          vstring s = "in "+f->toString()+" there is other connective than and! \n This is not supported! ";
          USER_ERROR(s);
      }
    }
  //collect all the atoms from the formula
  Stack<Literal*> litStack;
  form->collectAtoms(litStack);

  for(unsigned idx = 0 ; idx < litStack.size(); idx++){
      ConstraintRCPtr constraint = getConstraint(litStack[idx]);
      ConstraintRCList::push(constraint, res);
  }

  return res;
}

ConstraintRCPtr SMTLib2ConstraintReader::getConstraint(Literal* literal) {
	CALL("SMTLib2ConstraintReader::getConstraint(Literal* )");
	ConstraintType constraintType = CT_EQ;
	vstring predName = literal->predicateName();
	if (predName == "$greatereq") {
		constraintType = CT_GREQ;
	} else {
		if (predName == "=") {
			constraintType == CT_EQ;
		} else if (predName == "$greater") {
			constraintType = CT_GR;
		} else {
			USER_ERROR("predicate >, >= or = expected");
		}
	}

	Term* term(literal);
	CoefficientStack cStack;
	CoeffNumber freeCoef = CoeffNumber::zero();

	ASS(term->arity()==2);
	Term::Iterator tit(term);
	TermList lhs = tit.next();
	TermList rhs = tit.next();

	if (isNumber(lhs.toString())) {
		if (lhs.term()->functionName() == "$uminus") {
			freeCoef = freeCoef - CoeffNumber(lhs.term()->args()->toString());
		} else {
			freeCoef = freeCoef + CoeffNumber(lhs.toString());
		}
		readCoefficients(rhs.term(), cStack, freeCoef, CoeffNumber(-1));
	} else {
		if (isNumber(rhs.toString())) {
			readCoefficients(lhs.term(), cStack, freeCoef);
			if (rhs.term()->functionName() == "$uminus") {
				freeCoef = freeCoef
						+ CoeffNumber(rhs.term()->args()->toString());
			} else {
				freeCoef = freeCoef - CoeffNumber(rhs.toString());
			}
		} else {
			readCoefficients(lhs.term(), cStack, freeCoef);
			CoeffNumber secondFree = CoeffNumber::zero();
			readCoefficients(rhs.term(),cStack, secondFree, CoeffNumber(-1));
			freeCoef = freeCoef - secondFree;
		}

	}
	//create the constraint from the stack of coefficients
	ConstraintRCPtr crp(
			Constraint::fromIterator(constraintType,
					pvi(CoefficientStack::Iterator(cStack)), freeCoef));
	return crp;
}

void SMTLib2ConstraintReader::readCoefficients(Term* term,
		CoefficientStack& coeff, CoeffNumber& freeCoef, CoeffNumber value) {
	CALL("SMTLib2ConstraintReader::readCoefficients()");

	//this means we have only a single variable as a constraint
	if (term->functionName() == "$sum") {
		ASS(term->args()!=0);
		Term::Iterator tit(term);
		while (tit.hasNext()) {
			TermList tl = tit.next();
			Term* tt = tl.term();
			readCoefficients(tt, coeff, freeCoef);
		}
	} else {
		if (term->functionName() == "$product") {
			ASS(term->arity()==2);

			TermList* tl = term->args();
			TermList* val = tl->next();
			Var var;
			CoeffNumber coef;
			if (tl->term()->functionName() == "$uminus") {
				coef = CoeffNumber(-1)
						* CoeffNumber(tl->term()->args()->toString());
				var = _sig.addVar(val->toString());
			} else if (val->term()->functionName() == "$uminus") {
				coef = CoeffNumber(-1)
						* CoeffNumber(val->term()->args()->toString());
				var = _sig.addVar(tl->toString());
			} else {
				if (isNumber(tl->toString())) {
					coef = readNumber(tl->term());
					var = _sig.addVar(val->toString());
				} else {
					coef = readNumber(val->term());
					var = _sig.addVar(tl->toString());
				}
			}
			coeff.push(Constraint::Coeff(var, value*coef));

		} else {
			if (isNumber(term->toString())) {
				freeCoef = freeCoef + readNumber(term);
			} else {
				Var var = _sig.addVar(term->toString());
				coeff.push(Constraint::Coeff(var, value*CoeffNumber(1)));
			}
		}
	}
}

/**
 * Helping function which decides whether a string represents a number or not.
 * This function is not intended to work with hexadecimal numbers!
 * @param term the vstring to be checked if it is a number
 * @return true if the vstring is a number and false otherwise
 **/

bool SMTLib2ConstraintReader::isNumber(vstring term) {
	CALL("SMTLIB2ConstraintReader::isNumber");

	const char* str = term.c_str();
	int withDecimal = 0, isNegative = 0, i = 0;
	int len = strlen(str);

	for (i = 0; i < len; i++) {
		if (!isdigit(str[i])) //if1
				{
			if (str[i] == '.') {
				if (withDecimal) {
					return 0;
				}
				withDecimal = 1;
			} else if (str[i] == '-') {
				if (isNegative) {
					return 0;
				}
				if (i == 0) {
					isNegative = 1;
				} else {
					return 0;
				}

			} else {
				return 0;
			}
		} //end if1
	} // end for
	return 1;
}

CoeffNumber SMTLib2ConstraintReader::readNumber(Term* term){
	CALL("SMTLib2ConstraintReader::readNumber()");
	return CoeffNumber(term->toString());
}

SMTConstraintReader::SMTConstraintReader(SMTLIB& parser)
: _parser(parser){}

ConstraintRCList* SMTConstraintReader::constraints(){
  CALL("SMTConstraintReader::constraint()");
  ConstraintRCList* res = 0;

  return res;
}

ConstraintReader::ConstraintReader(SMTParser& parser)
 : _sig(*env.signature), _parser(parser) {}
 
/**
 * Return list of constraints from @c _parser
 */
ConstraintRCList* ConstraintReader::constraints()
{
  CALL("ConstraintReader::constraints");
    
  SMTParser::Benchmark* bench = _parser.benchmark();
  
  unsigned var = 0;
  for (SMTParser::FunctionDeclaration* decs = bench->functionDeclarations;
       decs;
       decs = decs->next) {
    _sig.addVar(decs->name);
  }

  ConstraintRCList* res = 0;

  SMTParser::Formula* form = bench->formula;
  if (form->connective != SMTParser::AND) {
    USER_ERROR("connective 'and' expected");
  }


  CoeffStack coeffs(var+1);
  for (form = form->args; form; form = form->next){
    if (form->connective != SMTParser::ATOM) {
      USER_ERROR("atomic formula expected");
    }
    SMTParser::Atom* atom = form->atom;
    CoeffNumber freeCoeff = CoeffNumber::zero();

    readCoefs(atom->args, coeffs, freeCoeff);

    ConstraintType constrType=CT_EQ;
    if (atom->pred == ">="){
      constrType = CT_GREQ;
    }
    else if (atom->pred == "="){
      constrType = CT_EQ;
    }
    else if (atom->pred == ">"){
      constrType = CT_GR;
    }
    else {
      USER_ERROR("predicate >, >= or = expected");
    }

    if(atom->args->next->fun!="0") {
      USER_ERROR("rhs must be zero");
    }

    //the freeCoeff is negative since in the constraint semantics it is on the RHS of the inequality
    //(while in the SMT file it is on the LHS)

    ConstraintRCPtr c(Constraint::fromIterator(constrType, pvi( CoeffStack::Iterator(coeffs) ), -freeCoeff));
    ConstraintRCList::push(c, res);
    coeffs.reset();

  }

  return res;
}

/**
 * Read a number from the representation of SMTParser
 */
CoeffNumber ConstraintReader::readNumber(SMTParser::Term* term)
{
  if (term->fun == "~"){
    ASS_EQ(term->args->next, 0);
    return -CoeffNumber(term->args->fun);
  }
  else{
    ASS(term->args == 0);
    return CoeffNumber(term->fun);
  };
}

/**
 * Read coefficients of a constraint from an SMTParser::Term object
 */
void ConstraintReader::readCoefs(SMTParser::Term* term, CoeffStack& coeffs, CoeffNumber& freeCoeff)
{
  CALL("ConstraintReader::readCoefs");

  if (term->fun == "+"){
    ASS(term->args != 0);
    readCoefs(term->args, coeffs, freeCoeff);
  }
  else{
    if (term->fun == "*"){
      SMTParser::Term* numTerm = term->args;
      SMTParser::Term* varTerm = numTerm->next;
      ASS(numTerm != 0);
      CoeffNumber coeffVal = readNumber(numTerm);
      ASS(varTerm != 0);
      Var var = _sig.addVar(varTerm->fun);
      coeffs.push(Constraint::Coeff(var, coeffVal));
      if (term->next != 0){
          readCoefs(term->next, coeffs, freeCoeff);
      }
    }
    else{
      freeCoeff += readNumber(term);
      if (term->next != 0){
          readCoefs(term->next, coeffs, freeCoeff);
      }
    }
  }
}

MpsConstraintReader::MpsConstraintReader(Model& model)
    : _sig(*env.signature), _model(model){ }

MpsConstraintReader::~MpsConstraintReader()
{
}

#define INFBOUND          1e20

ConstraintRCList* MpsConstraintReader::constraints(){
    CALL("MpsConstraintReader::constraints()");
    ConstraintRCList* res = 0;
  
   std::map<vstring, Variable*>::const_iterator vitr = _model.vars.begin();
   std::map<vstring, Variable*>::const_iterator vend = _model.vars.end();
   CoeffStack coeff(1);
    
   while( vitr != vend )
   {
       if(!vitr->second->objCoef.isZero())
	coeff.push(Constraint::Coeff(_sig.addVar(vitr->second->name), CoeffNumber(vitr->second->objCoef.toDouble())));    
      ++vitr;
   }
   ConstraintRCPtr c(Constraint::fromIterator(CT_GR, pvi(CoeffStack::Iterator(coeff)),CoeffNumber::zero() ));
   ConstraintRCList::push(c,res);
   
   std::map<vstring, BaseConstraint*>::const_iterator citr = _model.conss.begin();
   std::map<vstring, BaseConstraint*>::const_iterator cend = _model.conss.end();
   
   unsigned var = 0;
   CoeffStack coefficients(var+1), negatedCoeff(var+1);
   
   
   while( citr != cend )
   {
      LinearConstraint* lcons = static_cast<LinearConstraint*>(citr->second);
      std::vector<Variable*> variables(lcons->vars);
      std::vector<gmpRational> coef(lcons->coefs);

      for (unsigned i = 0 ; i < variables.size() ; ++i)
      {
	Var varible = _sig.addVar(variables[i]->name);
	double a = coef[i].toDouble(); 
	if(a!=0){
	  coefficients.push(Constraint::Coeff(varible, CoeffNumber(a)));
	  negatedCoeff.push(Constraint::Coeff(varible, -CoeffNumber(a)));
	}
      }
    
      CoeffNumber freeUp, freeCoeff;
      //ConstraintRCPtr c, c1;
      switch(lcons->lintype)
      {
	  case LinearConstraint::LESS_THAN: 
	  {
	      /**
	       * We store constraint <= bound as 
	       * -constraint >= -bound
	       */
	      freeUp = -CoeffNumber((lcons->rhs.toDouble()));
	      ConstraintRCPtr c1(Constraint::fromIterator(CT_GREQ, pvi(CoeffStack::Iterator(negatedCoeff)),freeUp));
	      ConstraintRCList::push(c1,res);
	      break;
	  }
	  case LinearConstraint::GREATER_THAN:
	  {
	      /**
	       * We actually store the exact constraint 
	       * constraint >= bound CT_GREQ
	       */
	     freeCoeff = CoeffNumber(lcons->lhs.toDouble());
	      ConstraintRCPtr c(Constraint::fromIterator(CT_GREQ, pvi(CoeffStack::Iterator(coefficients)),freeCoeff));
	      ConstraintRCList::push(c,res); 
	      break ;
	  }
	  case LinearConstraint::EQUAL:
	  case LinearConstraint::RANGED:
	  {
	      /**
	       * This should be stores in a similar way as equal but 
	       * we have both upper and lower bound set.
	       */
	      // -bound >= -rhs
	      freeUp = -CoeffNumber(lcons->rhs.toDouble());
	      ConstraintRCPtr c1(Constraint::fromIterator(CT_GREQ, pvi(CoeffStack::Iterator(negatedCoeff)),freeUp));
	      ConstraintRCList::push(c1,res);
	      // bound >= lhs
	      freeCoeff = CoeffNumber(lcons->lhs.toDouble());
	      ConstraintRCPtr c(Constraint::fromIterator(CT_GREQ, pvi(CoeffStack::Iterator(coefficients)),freeCoeff));
	      ConstraintRCList::push(c,res); 
	      break; 
	  }
	  default: 
	      USER_ERROR("Constraints unbounded");
      }        
      ++citr;
        
      coefficients.reset();
      negatedCoeff.reset();
   }
   
   //_model.print(std::cout); 
    
   vitr = _model.vars.begin();
   vend = _model.vars.end();
   while( vitr != vend )
   {
      CoeffStack coef(1);
      if (vitr->second->lb != -INFBOUND)
      {
	CoeffNumber free = CoeffNumber(vitr->second->lb.toDouble());
	
	coef.push(Constraint::Coeff(_sig.addVar(vitr->second->name),CoeffNumber(1)));
	ConstraintRCPtr cons(Constraint::fromIterator(CT_GREQ, pvi(CoeffStack::Iterator(coef)), free));
	ConstraintRCList::push(cons, res);
	coef.reset();
	}
	
     if(vitr->second->ub != INFBOUND ) 
     {
	 CoeffNumber free = CoeffNumber(vitr->second->ub.toDouble());
	 
	 coef.push(Constraint::Coeff(_sig.addVar(vitr->second->name),CoeffNumber::minusOne()));
	 ConstraintRCPtr cons(Constraint::fromIterator(CT_GREQ, pvi(CoeffStack::Iterator(coef)), -free));
	 ConstraintRCList::push(cons, res);
	 coef.reset();
    }
    //  vitr->second->print(cout);
      ++vitr;
   }
    return res;
}

#endif //GNUMP
