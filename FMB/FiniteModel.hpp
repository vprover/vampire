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
 * @file FiniteModel.hpp
 * Defines class for finite models
 *
 * @since 26/09/2015 Manchester
 * @author Giles
 */

#ifndef __FiniteModel__
#define __FiniteModel__

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Term.hpp"


namespace FMB {

using namespace Lib;
using namespace Kernel;

/**
 *
 *
 */
class FiniteModel {
 CLASS_NAME(FiniteModel);
 USE_ALLOCATOR(FiniteModel);

public:

 const unsigned _size;
 FiniteModel(unsigned size);

 // Assume def is an equality literal with a
 // function application on lhs and constant on rhs
 void addConstantDefinition(unsigned f, unsigned res);
 void addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res); 
 // Assume def is non-equality ground literal
 void addPropositionalDefinition(unsigned f, bool res);
 void addPredicateDefinition(unsigned f, const DArray<unsigned>& args, bool res); 

 bool isPartial();

 bool evaluate(Unit* unit);
 unsigned evaluateGroundTerm(Term* term);
 bool evaluateGroundLiteral(Literal* literal);

 vstring toString();

private:

 Formula* partialEvaluate(Formula* formula);
 // currently private as requires formula to be rectified
 bool evaluate(Formula* formula,unsigned depth=0);

 // The model is partial if there is a operation with arity n that does not have
 // coverage size^n in its related coverage map
 bool _isPartial;
 DHMap<unsigned,unsigned> _functionCoverage;
 DHMap<unsigned,unsigned> _predicateCoverage;

 DArray<unsigned> f_offsets;
 DArray<unsigned> p_offsets;
 DArray<unsigned> f_interpretation;
 DArray<unsigned> p_interpretation; // 0 is undef, 1 false, 2 true

 DHMap<unsigned,Term*> _domainConstants;
 DHMap<Term*,unsigned> _domainConstantsRev;
public:
 Term* getDomainConstant(unsigned c)
 {
   Term* t;
   if(_domainConstants.find(c,t)) return t;
   vstring name = "domainConstant";//+Lib::Int::toString(c);
   unsigned f = env.signature->addFreshFunction(0,name.c_str()); 
   t = Term::createConstant(f);
   _domainConstants.insert(c,t);
   _domainConstantsRev.insert(t,c);

   return t;
 }
 unsigned getDomainConstant(Term* t)
 {
   unsigned c;
   if(_domainConstantsRev.find(t,c)) return c;
   USER_ERROR("Evaluated to "+t->toString()+" when expected a domain constant, probably a partial model");
 }
 bool isDomainConstant(Term* t)
 {
   return _domainConstantsRev.find(t);
 }

};


} // namespace FMB
#endif
