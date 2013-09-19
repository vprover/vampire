/**
 * @file ConstraintReader.cpp
 * Implements class ConstraintReader.
 */
#if GNUMP

#include <string>
#include <fstream>

#include "Lib/Environment.hpp"
#include "Lib/RCPtr.hpp"
#include "Shell/Options.hpp"
#include "Kernel/Number.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Clause.hpp"

#include "SMTPAR.hpp"
#include "Parse/SMTLIB.hpp"
#include "ConstraintReaderBack.hpp"

namespace Shell
{

using namespace Kernel;
using namespace Parse;
using namespace std;

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

    ConstraintType constrType;
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
  
   std::map<std::string, Variable*>::const_iterator vitr = _model.vars.begin();
   std::map<std::string, Variable*>::const_iterator vend = _model.vars.end();
   CoeffStack coeff(1);
    
   while( vitr != vend )
   {
       if(!vitr->second->objCoef.isZero())
	coeff.push(Constraint::Coeff(_sig.addVar(vitr->second->name), CoeffNumber(vitr->second->objCoef.toDouble())));    
      ++vitr;
   }
   ConstraintRCPtr c(Constraint::fromIterator(CT_GR, pvi(CoeffStack::Iterator(coeff)),CoeffNumber::zero() ));
   ConstraintRCList::push(c,res);
   
   std::map<std::string, BaseConstraint*>::const_iterator citr = _model.conss.begin();
   std::map<std::string, BaseConstraint*>::const_iterator cend = _model.conss.end();
   
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

}
#endif //GNUMP
