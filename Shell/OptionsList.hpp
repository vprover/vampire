/**
 * @file OptionsList.hpp
 * Defines list of options
 * 
 */

#ifndef __OptionsList__
#define __OptionsList__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Shell/Options.hpp"

namespace Shell {

using namespace Lib;

/**
 * For storing multiple options for many strategies
 * Requires us to know the number of strategies up-front
 *
 * @author Giles
 * @since 13/05/2014
 */

class OptionsList 
{

public:
  inline OptionsList(unsigned len) : _length(len), _alive(0){
    CALL("OptionsList::OptionsList()");
    ASS(len>0);
    void* mem = ALLOC_KNOWN(len*sizeof(Options),"OptionsList");
    // Initialises _strategies by calling constructor of Options
    _strategies = array_new<Options>(mem,len);
  }
  ~OptionsList(){
    CALL("OptionsList::~OptionsList()");
    cout << "destroying optionslist" << endl;
    array_delete(_strategies,_length);
    DEALLOC_KNOWN(_strategies,_length*sizeof(Options),"OptionsList");
  }


  typedef ArrayishObjectIterator<OptionsList> Iterator;
  DECL_ELEMENT_TYPE(Options&);
  DECL_ITERATOR_TYPE(Iterator);

  /** Return the number of strategies **/
  unsigned size() const {return _length;}
  /** Return the nth strategy **/
  Options& operator[](unsigned n) const { return _strategies[n]; }
  /** Return an iterator for the live strategies
      A strategy is live if it has been given individual options
      If strategy n is live then all strategies m<n are live **/
  ArrayishObjectIterator<OptionsList> getLive() {
    return ArrayishObjectIterator<OptionsList>(*this,_alive);
  }

  /** Update the number of live strategies **/
  void setLive(unsigned n){
    if(n > _alive){
      _alive = n+1;
    }
  }

  /** Include a new options file
      If this includes global options these will apply to
      live strategies only **/
  void include(const string& newVal);

  //Functions for setting global options
  void set(const string& name, const string& value);
  void set(const char* name, const char* value);
  void setShort(const char* name, const char* value);
  void setInputFile(const string& newVal);

  //Functions for setting local options
  void set(unsigned n, const string& name, const string& value)
  { check(n);(*this)[n].set(name,value); setLive(n); }
  void set(unsigned n, const char* name, const char* value)
  { check(n);(*this)[n].set(name,value); setLive(n); }
  void setShort(unsigned n, const char* name, const char* value)
  { check(n);(*this)[n].setShort(name,value); setLive(n); }

  //Final functions
  void setForcedOptionValues();
  void checkGlobalOptionConstraints();

private:

  void check(unsigned n){
    if(n >= _length){ USER_ERROR("You are using more strategies than you said you would!"); }
  }

  unsigned _length;
  unsigned _alive;
  Options* _strategies;

}; // class OptionsList


}

#endif
