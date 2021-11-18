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
 * @file FiniteModelMultiSorted.hpp
 * Defines class for finite models
 *
 * @since 6/01/2016 Manchester
 * @author Giles
 */

#ifndef __FiniteModelMultiSorted__
#define __FiniteModelMultiSorted__

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
class FiniteModelMultiSorted {
 CLASS_NAME(FiniteModelMultiSorted);
 USE_ALLOCATOR(FiniteModelMultiSorted);

 DHMap<unsigned,unsigned> _sizes;

public:

 // sortSizes is a map from vampire sorts (defined in Kernel/Sorts) to the size of that sort
 FiniteModelMultiSorted(DHMap<unsigned,unsigned> sortSizes);

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

 DArray<DArray<int>> sortRepr;

 DArray<unsigned> f_offsets;
 DArray<unsigned> p_offsets;
 DArray<unsigned> f_interpretation;
 DArray<unsigned> p_interpretation; // 0 is undef, 1 false, 2 true

 // the pairs of <constant number, sort>
 DHMap<pair<unsigned,unsigned>,Term*> _domainConstants;
 DHMap<Term*,pair<unsigned,unsigned>> _domainConstantsRev;
public:
 Term* getDomainConstant(unsigned c, unsigned srt)
 {
   Term* t;
   pair<unsigned,unsigned> pair = make_pair(c,srt);
   if(_domainConstants.find(pair,t)) return t;
   vstring name = "domCon_"+env.signature->typeConName(srt)+"_"+Lib::Int::toString(c);
   unsigned f = env.signature->addFreshFunction(0,name.c_str()); 
   TermList srtT = TermList(AtomicSort::createConstant(srt));
   env.signature->getFunction(f)->setType(OperatorType::getConstantsType(srtT));
   t = Term::createConstant(f);
   _domainConstants.insert(pair,t);
   _domainConstantsRev.insert(t,pair);

   return t;
 }
 pair<unsigned,unsigned> getDomainConstant(Term* t)
 {
   pair<unsigned,unsigned> pair;
   if(_domainConstantsRev.find(t,pair)) return pair;
   USER_ERROR("Evaluated to "+t->toString()+" when expected a domain constant, probably a partial model");
 }
 bool isDomainConstant(Term* t)
 {
   return _domainConstantsRev.find(t);
 }
 vstring prepend(const char* prefix, vstring name) {
   if (name.empty()) {
     return vstring(prefix);
   } else if (name[0] == '\'') {
     vstring dequoted = name.substr(1, name.length() - 1);
     return vstring("'") + prefix + dequoted;
   } else {
     return prefix + name;
   }
 }
 vstring append(vstring name, const char* suffix) {
   if (name.empty()) {
     return vstring(suffix);
   } else if (name[0] == '\'') {
     vstring dequoted = name.substr(0, name.length() - 1);
     return dequoted + suffix + "'";
   } else {
     return name + suffix;
   }
 }
};


} // namespace FMB
#endif
