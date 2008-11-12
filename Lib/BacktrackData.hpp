/**
 * @file BacktrackData.hpp
 * Defines class BacktrackData
 */

#ifndef __BacktrackData__
#define __BacktrackData__

#include "List.hpp"


namespace Lib
{

class BacktrackObject
{
public:
  virtual ~BacktrackObject() {}
  virtual void backtrack() = 0;
};

class BacktrackData
{
public:
  BacktrackData() : _bol(0) {}
  void backtrack()
  {
    while(_bol) {
      _bol->head()->backtrack();
      delete _bol->head();
      
      List<BacktrackObject*>* par;
      par=_bol;
      _bol=par->tail();
      delete par;
    }
  }
  void drop()
  {
    _bol->destroyWithDeletion();
    _bol=0;
  }
  void addBacktrackObject(BacktrackObject* bo)
  {
    _bol=new List<BacktrackObject*>(bo, _bol);
  }
  /**
   * Move all BacktrackObjects from @b this to @b bd. After the
   * operation, @b this is empty.   
   */
  void commitTo(BacktrackData& bd)
  {
    _bol=List<BacktrackObject*>::concat(bd._bol, _bol);
    bd._bol=0;
  }
  
private:
  List<BacktrackObject*>* _bol;
};

};

#endif // __BacktrackData__
