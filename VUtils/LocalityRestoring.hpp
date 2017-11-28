
/*
 * File LocalityRestoring.hpp.
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
 * @file LocalityRestoring.hpp
 * Defines class LocalityRestoring.
 */

#ifndef __LocalityRestoring__
#define __LocalityRestoring__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Stack.hpp"



namespace VUtils {

using namespace Lib;
using namespace Kernel;

class LocalityRestoring {
public:
  LocalityRestoring(bool quantLeft, UnitStack& derivation, UnitStack& target);

  bool perform();

  static bool isLocalDerivation(Unit* refutation);
private:

  struct CompRecord;

  static Unit* getUnitWithMappedInference(Unit* u, DHMap<Unit*,Unit*>& map, UnitList* premisesToAdd=0,
      DHSet<Unit*>* allowedPremises=0);


  //top level functions
  void buildNSC();
  void collectColorsAndLocality();
  void processComponents();

  //helpers for buildNSC()
  static void collectColoredTerms(Unit* u, TermStack& acc);
  static void collectSCTerms(Unit* u, TermStack& acc);
  static Unit* makeNSCPremise(TermList trm);


  //helpers for collectColorsAndLocality()
  static Color getColor(Unit* u);
  bool isLocal(Unit* u);
  bool shouldProcess(Unit* u);
  void scanForProcessing(Unit* u, IntUnionFind& procComponentUF);
  void addComponent(UnitStack& units);

  //helpers for processComponents()
  class QuantifyingTermTransformer;
  class FormulaSimplifier;
  class FringeKeeper;
  static Unit* copyWithNewInference(Unit* u, Inference* inf);
  void processComponent(CompRecord& comp);



  Color _quantifiedColor;
  Color _nonQuantifiedColor;



  DHMap<Unit*,Unit*> _nscConversionMap;

  /** initialized in collectColorsAndLocality() */
  DHMap<Unit*, Color>  _unitColors;

  /** initialized in collectColorsAndLocality() */
  bool _allLocal;
  /** initialized in collectColorsAndLocality() */
  DHMap<Unit*, bool>  _unitLocality;

  /**
   * Units that will be members of some processing component
   *
   * initialized in collectColorsAndLocality()
   */
  DHSet<Unit*> _toBeProcessed;

  Stack<CompRecord*> _comps;

  DHMap<Unit*,Unit*> _processingResultMap;
  DHMap<Unit*,Unit*> _initialFringeTriggerringMap;
  DHMap<Unit*,Unit*> _fringePremiseTriggerringMap;
  DHMap<Unit*,Unit*> _localConversionMap;


  UnitStack& _der;
  /** nsc ~ no surprising colors. Derivation where colored formulas
   * have at least one premise of the same color*/
  UnitStack _nscDer;
  UnitStack _locDer;
  UnitStack& _tgt;
};

}

#endif // __LocalityRestoring__
