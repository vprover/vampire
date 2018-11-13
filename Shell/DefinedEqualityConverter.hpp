
/*
 * File DefinedEqualityConverter.hpp.
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
 * @file DefinedEqualityConverter.hpp
 * Defines class DefinedEqualityConverter.
 */


#ifndef __DefinedEqualityConverter__
#define __DefinedEqualityConverter__

#include "Forwards.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/HOSortHelper.hpp"
#include "Kernel/Signature.hpp"

#include "Inferences/ProxyElimination.hpp"

namespace Shell {

using namespace std;
using namespace Lib;
using namespace Kernel;


class DefinedEqualityConverter
{
public:
  DefinedEqualityConverter();

  void convert(Problem& prb);
  void convert(UnitList*& units);

private:

  /* [X1 a = true] 
     var = X1,
     polarity = 1
     side = 0;

     arg = a ... 
  */
  struct LeibEqRec {
    unsigned var;
    unsigned polarity;
    unsigned side;

    unsigned argSort;
    TermList arg;
    
    Literal* lit;
  };

  typedef HOSortHelper HSH;
  typedef DHMap<unsigned, LeibEqRec> VarOccMap;
  typedef Signature::Symbol SS;
  typedef Inferences::ProxyElimination PE;

  //Andrews Equality
  bool isAndrewsEquality(Literal*, unsigned&);
  TermList getAndrewsDef(Literal*, unsigned);
  unsigned getVar(Literal*, unsigned);

  //Leibniz Equality
  bool isLeibnizEquality(Literal*, LeibEqRec&);
  Literal* createEquality(LeibEqRec,LeibEqRec);
  TermList getLeibnizDef(LeibEqRec);

  /**
    * Scans clause c for instances of defined equalities
    * and produces a resulting clause with these instances
    * replaced with primitive equality
    */
  Clause* findAndConvert(Clause* c);

};

};

#endif /* __DefinedEqualityConverter__ */
