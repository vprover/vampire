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

  void discoverColors();
  bool isLocal(Unit* u);

  Color getColor(Unit* u);
  void extractComponents();

  bool _allLocal;

  DHMap<Unit*, unsigned> _unitIndexes;
  Stack<Color> _colors;
  Stack<bool> _nonLocal;

  Stack<Unit*>& _der;
  Stack<Unit*>& _tgt;
  Stack<CompRecord> _comps;
};

}

#endif // __LocalityRestoring__
