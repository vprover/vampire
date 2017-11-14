
/*
 * File ConstraintReaderBack.hpp.
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
 * @file ConstraintReaderBack.hpp
 * Defines class ConstraintReader and related classes
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
  bool isNumber(vstring term);
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


