/**
 * @file BacktrackData.hpp
 * Defines class BacktrackData
 */

#ifndef __BacktrackData__
#define __BacktrackData__

#include "List.hpp"

#ifdef VDEBUG
#include <string>
#include "Int.hpp"
#endif


namespace Lib
{

class BacktrackObject
{
public:
  virtual ~BacktrackObject() {}
  virtual void backtrack() = 0;
  
#ifdef VDEBUG
  virtual std::string toString() { return "(backtrack object)"; }
#endif
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
    bd._bol=List<BacktrackObject*>::concat(_bol,bd._bol);
    _bol=0;
  }
  
#ifdef VDEBUG
  std::string toString()
  {
    std::string res;
    List<BacktrackObject*>* boit=_bol;
    int cnt=0;
    while(boit) {
      res+=boit->head()->toString()+"\n";
      cnt++;
      boit=boit->tail();
    }
    res+="object cnt: "+Int::toString(cnt)+"\n";
    return res;
  }
#endif
  
private:
  List<BacktrackObject*>* _bol;
};

class Backtrackable
{
public:
  Backtrackable() : _bdStack(0) {}
  void bdRecord(BacktrackData& bd)
  {
    _bdStack=new List<BacktrackData*>(&bd, _bdStack);
  }
  void bdDoNotRecord()
  {
    _bdStack=new List<BacktrackData*>(0, _bdStack);
  }
  void bdDone()
  {
    List<BacktrackData*>::pop(_bdStack);
  }
protected:
  bool bdIsRecording()
  {
    return _bdStack && _bdStack->head();
  }
  void bdAdd(BacktrackObject* bo)
  {
    bdGet().addBacktrackObject(bo);
  }
  void bdCommit(BacktrackData& bd)
  {
    bd.commitTo(bdGet());
  }
  BacktrackData& bdGet()
  {
    ASS(_bdStack && _bdStack->head());
    return *_bdStack->head();
  }
private:
  List<BacktrackData*>* _bdStack;
};

};

#endif // __BacktrackData__
