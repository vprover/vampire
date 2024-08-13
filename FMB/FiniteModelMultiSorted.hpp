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

using namespace Kernel;

/**
 *
 *
 */
class FiniteModelMultiSorted {
 Lib::DHMap<unsigned,unsigned> _sizes;

public:

 // sortSizes is a map from vampire sorts (defined in Kernel/Sorts) to the size of that sort
 FiniteModelMultiSorted(Lib::DHMap<unsigned,unsigned> sortSizes);

 // Assume def is an equality literal with a
 // function application on lhs and constant on rhs
 void addConstantDefinition(unsigned f, unsigned res);
 void addFunctionDefinition(unsigned f, const Lib::DArray<unsigned>& args, unsigned res); 
 // Assume def is non-equality ground literal
 void addPropositionalDefinition(unsigned f, bool res);
 void addPredicateDefinition(unsigned f, const Lib::DArray<unsigned>& args, bool res); 

 bool isPartial();

 bool evaluate(Unit* unit);
 unsigned evaluateGroundTerm(Term* term);
 bool evaluateGroundLiteral(Literal* literal);

 std::string toString();

private:

 Formula* partialEvaluate(Formula* formula);
 // currently private as requires formula to be rectified
 bool evaluate(Formula* formula,unsigned depth=0);

 // The model is partial if there is a operation with arity n that does not have
 // coverage size^n in its related coverage map
 bool _isPartial;
 Lib::DHMap<unsigned,unsigned> _functionCoverage;
 Lib::DHMap<unsigned,unsigned> _predicateCoverage;

 Lib::DArray<Lib::DArray<int>> sortRepr;

 Lib::DArray<unsigned> f_offsets;
 Lib::DArray<unsigned> p_offsets;
 Lib::DArray<unsigned> f_interpretation;
 Lib::DArray<unsigned> p_interpretation; // 0 is undef, 1 false, 2 true

 // the pairs of <constant number, sort>
 Lib::DHMap<std::pair<unsigned,unsigned>,Term*> _domainConstants;
 Lib::DHMap<Term*,std::pair<unsigned,unsigned>> _domainConstantsRev;
public:
 Term* getDomainConstant(unsigned c, unsigned srt)
 {
   Term* t;
   std::pair<unsigned,unsigned> pair = std::make_pair(c,srt);
   if(_domainConstants.find(pair,t)) return t;
   std::string name = "domCon_"+Lib::env.signature->typeConName(srt)+"_"+Lib::Int::toString(c);
   unsigned f = Lib::env.signature->addFreshFunction(0,name.c_str()); 
   TermList srtT = TermList(AtomicSort::createConstant(srt));
   Lib::env.signature->getFunction(f)->setType(OperatorType::getConstantsType(srtT));
   t = Term::createConstant(f);
   _domainConstants.insert(pair,t);
   _domainConstantsRev.insert(t,pair);

   return t;
 }
 std::pair<unsigned,unsigned> getDomainConstant(Term* t)
 {
   std::pair<unsigned,unsigned> pair;
   if(_domainConstantsRev.find(t,pair)) return pair;
   USER_ERROR("Evaluated to "+t->toString()+" when expected a domain constant, probably a partial model");
 }
 bool isDomainConstant(Term* t)
 {
   return _domainConstantsRev.find(t);
 }
 std::string prepend(const char* prefix, std::string name) {
   if (name.empty()) {
     return std::string(prefix);
   } else if(name[0] == '$') {
     return std::string("'") + prefix + name + "'";
   } else if (name[0] == '\'') {
     std::string dequoted = name.substr(1, name.length() - 1);
     return std::string("'") + prefix + dequoted;
   } else {
     return prefix + name;
   }
 }
 std::string append(std::string name, const char* suffix) {
   if (name.empty()) {
     return std::string(suffix);
   } else if(name[0] == '$') {
     return std::string("'") + name + suffix + "'";
   } else if (name[0] == '\'') {
     std::string dequoted = name.substr(0, name.length() - 1);
     return dequoted + suffix + "'";
   } else {
     return name + suffix;
   }
 }
};


} // namespace FMB
#endif
