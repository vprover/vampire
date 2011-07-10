/**
 * @file LocalityRestoring.hpp
 * Defines class LocalityRestoring.
 */

#ifndef __LocalityRestoring__
#define __LocalityRestoring__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"
#include "Lib/DHMap.hpp"



namespace VUtils {

using namespace Lib;
using namespace Kernel;

class LocalityRestoring {
public:
  LocalityRestoring(Stack<Unit*>& derivation, Stack<Unit*>& target);

  bool perform();
private:

  struct CompRecord
  {
    UnitList* fringe;
    List<unsigned>* members;
  };

  static Unit* getUnitWithMappedInference(Unit* u, DHMap<Unit*,Unit*>& map, UnitList* premisesToAdd);

  static void collectColoredTerms(Unit* u, TermStack& acc);
  static void collectSCTerms(Unit* u, TermStack& acc);
  static Unit* makeNSCPremise(TermList trm);

  //top level functions
  void buildNSC();
  void collectColorsAndLocality();


  Color getColor(Unit* u);
  bool isLocal(Unit* u);

  bool shouldProcess(Unit* u);

  void extractComponents();

  Color _quantifiedColor;

  /** Units that will be members of some processing component */
  DHSet<Unit*> _toBeProcessed;

  bool _allLocal;

  DHMap<Unit*, unsigned> _unitIndexes;

  DHMap<Unit*, Color>  _unitColors;
  DHMap<Unit*, bool>  _unitLocality;

  DHMap<Unit*,Unit*> _nscConversionMap;

  Stack<Unit*>& _der;
  /** nsc ~ no surprising colors. Derivation where colored formulas
   * have at least one premise of the same color*/
  Stack<Unit*> _nscDer;
  Stack<Unit*>& _tgt;
  Stack<CompRecord> _comps;
};

}

#endif // __LocalityRestoring__
