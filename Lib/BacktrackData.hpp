/**
 * @file BacktrackData.hpp
 * Defines class BacktrackData
 */

#ifndef __BacktrackData__
#define __BacktrackData__

#include "List.hpp"

#if VDEBUG
#include <string>
#include "Int.hpp"
#endif


namespace Lib
{

class BacktrackData;

class BacktrackObject
{
public:
#if VDEBUG
  BacktrackObject() : _next(0) {}
#endif
  virtual ~BacktrackObject()  {}

  virtual void backtrack() = 0;

#if VDEBUG
  virtual std::string toString() const { return "(backtrack object)"; }
#endif
private:
  BacktrackObject* _next;

  friend class BacktrackData;
};

class BacktrackData
{
public:
  BacktrackData() : _boList(0) {}
  void backtrack()
  {
    BacktrackObject* curr=_boList;
    BacktrackObject* next;
    while(curr) {
      curr->backtrack();
      next=curr->_next;
      delete curr;
      curr=next;
    }
    _boList=0;
  }
  void drop()
  {
    BacktrackObject* curr=_boList;
    BacktrackObject* next;
    while(curr) {
      next=curr->_next;
      delete curr;
      curr=next;
    }
    _boList=0;
  }
  void addBacktrackObject(BacktrackObject* bo)
  {
    ASS_EQ(bo->_next,0);
    bo->_next=_boList;
    _boList=bo;
  }
  /**
   * Move all BacktrackObjects from @b this to @b bd. After the
   * operation, @b this is empty.
   */
  void commitTo(BacktrackData& bd)
  {
    if(!_boList) {
      return;
    }
    BacktrackObject* lastOwn=_boList;
    while(lastOwn->_next) {
      lastOwn=lastOwn->_next;
    }
    lastOwn->_next=bd._boList;
    bd._boList=_boList;
    _boList=0;
  }

  bool isEmpty() const
  {
    return _boList==0;
  }

  template<typename T>
  void backtrackableSet(T* ptr, T val)
  {
    addBacktrackObject(new SetValueBacktrackObject<T>(ptr,*ptr));
    *ptr=val;
  }

#if VDEBUG
  std::string toString()
  {
    std::string res;
    unsigned cnt=0;
    BacktrackObject* bobj=_boList;
    while(bobj) {
      res+=bobj->toString()+"\n";
      cnt++;
      bobj=bobj->_next;
    }
    res+="object cnt: "+Int::toString(cnt)+"\n";
    return res;
  }
#endif
  BacktrackObject* _boList;
private:

  template<typename T>
  class SetValueBacktrackObject
  : public BacktrackObject
  {
  public:
    SetValueBacktrackObject(T* addr, T previousVal)
    : addr(addr), previousVal(previousVal) {}
    void backtrack()
    {
      *addr=previousVal;
    }
  private:
    T* addr;
    T previousVal;
  };
};

class Backtrackable
{
public:
  Backtrackable() : _bdStack(0) {}
#if VDEBUG
  ~Backtrackable() { ASS_EQ(_bdStack,0); }
#endif
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
    ASS_NEQ(&bd,&bdGet());
    bd.commitTo(bdGet());
  }
  BacktrackData& bdGet()
  {
    return *_bdStack->head();
  }
private:
  List<BacktrackData*>* _bdStack;
};

};

#endif // __BacktrackData__
