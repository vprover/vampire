/**
 * @file ConstraintReader.hpp
 * Defines class ConstraintReader.
 */

#ifndef __ConstraintReader__
#define __ConstraintReader__
#if GNUMP
#include "Forwards.hpp"

#include "Kernel/Constraint.hpp"
#include "MPSLib/Model.h"

#include "SMTPAR.hpp"

namespace Shell {

using namespace Kernel;

class ConstraintReader {
public:
  ConstraintReader(SMTParser& parser);
  
  ConstraintRCList* constraints();
private:
  typedef Stack<Constraint::Coeff> CoeffStack;

  void readCoefs(SMTParser::Term* term, CoeffStack& coeffs, CoeffNumber& freeCoeff);

  static CoeffNumber readNumber(SMTParser::Term* term);

  Signature& _sig;
  SMTParser& _parser; 
};

class SMTConstraintReader{
public:
  SMTConstraintReader(Parse::SMTLIB& parser);
  ConstraintRCList* constraints();
private:

  Parse::SMTLIB& _parser;
};

/**
 * Class designed in order to read constraints from smtlib2 format parser
 **/
class SMTLib2ConstraintReader{
public:
  SMTLib2ConstraintReader(Parse::SMTLIB2& parser);
  //returns the list of constraints
  ConstraintRCList* constraints();

private:

  typedef Stack<Constraint::Coeff> CoefficientStack;
  void readCoefficients(Term* term, CoefficientStack& coeffs, CoeffNumber& freeCoeff, CoeffNumber val=CoeffNumber(1));

  ConstraintRCPtr getConstraint(Literal* literal);
  CoeffNumber readNumber(Term* term);
  bool isNumber(string term);
  Signature& _sig;
  Parse::SMTLIB2& _parser;
};

class MpsConstraintReader
{

public:
    MpsConstraintReader(Model& model);
    virtual ~MpsConstraintReader();
    ConstraintRCList* constraints();

private: 
   typedef Stack<Constraint::Coeff> CoeffStack;
   Signature& _sig;
   Model& _model; 
   
};
}
#endif //GNUMP
#endif // __ConstraintReader__


