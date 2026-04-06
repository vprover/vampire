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
  DArray<unsigned> _sizes;

  static const char INTP_UNDEF = 0;
  static const char INTP_FALSE = 1;
  static const char INTP_TRUE = 2;

  // two big tables waiting to be filled with the intrepreations (of functions and predicates)
  DArray<unsigned> _f_offsets;
  DArray<unsigned> _p_offsets;
  DArray<unsigned> _f_interpretation;
  DArray<char> _p_interpretation; // 0 is undef, 1 false, 2 true

  // candidates for the domain constants in the model printed (we use existing constants of the respective sort, but introduce a new symbol, if there is none)
  // this is not the same thing (although, maybe, these could be unified?) as _domainConstants, which are used for evaluation
  DArray<DArray<int>> sortRepr;

  // uses _sizes to fillup _f/p_offsets and _f/p_interpretation from scratch
  // also cleans sortRepr (to be filled up from scratch)
  void initTables();

  // captures the encoding of the functions offsets and predicates in our tables
  // - offsets are either _f_offsets or _p_offsets
  // - s is either an f or p index from env->signature
  // - sig is the symbols corresponding type signature
  // - var is an index to use into _f_interpretation/_p_interpretation
  unsigned args2var(const DArray<unsigned>& args, const DArray<unsigned>& sizes,
                    const DArray<unsigned>& offsets, unsigned s, OperatorType* sig)
  {
    unsigned var = offsets[s];
    unsigned mult = 1;
    for(unsigned i=0;i<args.size();i++){
      var += mult*(args[i]-1);
      unsigned s = sig->arg(i).term()->functor();
      mult *=sizes[s];
    }
    return var;
  }

public:

  // sortSizes is a map from vampire sorts (defined in Kernel/Sorts) to the size of that sort
  FiniteModelMultiSorted(DArray<unsigned> sortSizes) : _sizes(std::move(sortSizes)) {
    initTables();
  }

  // Assume def is an equality literal with a
  // function application on lhs and constant on rhs
  void addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res);
  // Assume def is non-equality ground literal
  void addPredicateDefinition(unsigned f, const DArray<unsigned>& args, bool res);

  bool evaluate(Unit* unit, bool expectingPartial = false);
  unsigned evaluateGroundTerm(Term* term);
  bool evaluateGroundLiteral(Literal* literal);

  void eliminateSortFunctionsAndPredicates(const Stack<unsigned>& sortFunctions, const Stack<unsigned>& sortPredicates);
  void restoreEliminatedDefinitions(Kernel::Problem* prob);

  std::string toString();

private:
  unsigned evaluateTerm(TermList, const DHMap<unsigned,unsigned>& subst);
  bool evaluateLiteral(Literal*, const DHMap<unsigned,unsigned>& subst);
  bool evaluateFormula(Formula*, DHMap<unsigned,unsigned>& subst);

  // if term evaluation encounters a missing record, it assumes the corresponding symbol has been implicitly eliminated
  // (e.g., eliminated unused function definition f(X) = g(X,c) might have eliminated c, if it did not occur anywhere else)
  // such symbols are restored (just after restoreEliminatedDefinitions; although, formally it should happen before) in the simplest possible way:
  // functions == 1 (the first domain element of the respective sort) everywhere
  // predicates == false everywhere
  Set<unsigned> _implicitlyEliminatedFunctions;
  Set<unsigned> _implicitlyEliminatedPredicates;

  void restoreEliminatedFunDef(Problem::FunDef*);
  void restoreImplicitlyEliminatedFun(unsigned f);
  void restoreEliminatedPredDef(Problem::PredDef*);
  void restoreImplicitlyEliminatedPred(unsigned p);
  void restoreGlobalPredicateFlip(Problem::GlobalFlip*);
  void restoreViaCondFlip(Problem::CondFlip*);

  Formula* partialEvaluate(Formula* formula);
  // currently private as requires formula to be rectified
  bool evaluateOld(Formula* formula,unsigned depth=0);

  // the pairs of <constant number, sort>
  DHMap<std::pair<unsigned,unsigned>,Term*> _domainConstants;
  DHMap<Term*,std::pair<unsigned,unsigned>> _domainConstantsRev;
public:



  Term* getDomainConstant(unsigned c, unsigned srt)
  {
    Term* t;
    std::pair<unsigned,unsigned> pair = std::make_pair(c,srt);
    if(_domainConstants.find(pair,t)) return t;
    std::string name = "domCon_"+env.signature->typeConName(srt)+"_"+Lib::Int::toString(c);
    unsigned f = env.signature->addFreshFunction(0,name.c_str());
    TermList srtT = TermList(AtomicSort::createConstant(srt));
    env.signature->getFunction(f)->setType(OperatorType::getConstantsType(srtT));
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
