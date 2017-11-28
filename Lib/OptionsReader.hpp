
/*
 * File OptionsReader.hpp.
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
 * @file OptionsReader.hpp
 * Defines class OptionsReader.
 */

#ifndef __OptionsReader__
#define __OptionsReader__

#include "Forwards.hpp"

#include "DHMap.hpp"
#include "SmartPtr.hpp"
#include "Stack.hpp"

namespace Lib {

using namespace std;

class EnumReaderBase {
public:
  EnumReaderBase()
   : _vals(new DHMap<vstring,int>()), _names(new DHMap<int,vstring>())
  {
  }

  void addVal(vstring name, int val)
  {
    CALL("EnumReaderBase::addVal");
    ALWAYS(_vals->insert(name, val));
    ALWAYS(_names->insert(val, name));
  }
  bool tryRead(vstring name, int& val) const
  {
    CALL("EnumReaderBase::tryRead");
    return _vals->find(name, val);
  }
  vstring getValName(int val) const {
    return _names->get(val);
  }

  vstring toString() const {
    CALL("EnumReaderBase::toString");
    vstring res;
    DHMap<vstring,int>::Iterator valIt(*_vals);
    while(valIt.hasNext()) {
      vstring val = valIt.nextKey();
      res += val;
      if(valIt.hasNext()) {
	res+= ", ";
      }
    }
    return "["+res+"]";
  }

private:
  SmartPtr<DHMap<vstring,int> > _vals;
  SmartPtr<DHMap<int,vstring> > _names;
};

template<typename Enum>
class EnumReader : public EnumReaderBase {
public:
  void addVal(vstring name, Enum val)
  {
    CALL("EnumReader::addVal");

    EnumReaderBase::addVal(name, val);
  }
  bool tryRead(vstring name, Enum& val) const
  {
    int aux;
    if(!EnumReaderBase::tryRead(name, aux)) {
      return false;
    }
    val = static_cast<Enum>(aux);
    return true;
  }
};

class OptionsReader {
public:
  void registerStringOption(vstring* tgt, vstring name, vstring shortName=vstring()) {
    _longNames.push(name);
    ALWAYS(_stringOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_stringOptTargets.insert(shortName, tgt));
    }
  }

  void registerIntOption(int* tgt, vstring name, vstring shortName=vstring()) {
    _longNames.push(name);
    ALWAYS(_intOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_intOptTargets.insert(shortName, tgt));
    }
  }

  void registerUnsignedOption(unsigned* tgt, vstring name, vstring shortName=vstring()) {
    _longNames.push(name);
    ALWAYS(_unsignedOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_unsignedOptTargets.insert(shortName, tgt));
    }
  }

  void registerFloatOption(float* tgt,vstring name, vstring shortName=vstring()) {
    _longNames.push(name);
    ALWAYS(_floatOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_floatOptTargets.insert(shortName, tgt));
    }
  }

  void registerBoolOption(bool* tgt,vstring name, vstring shortName=vstring()) {
    _longNames.push(name);
    ALWAYS(_boolOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_boolOptTargets.insert(shortName, tgt));
    }
  }

  template<typename Enum>
  void registerEnumOption(Enum* tgt, EnumReaderBase enumVals, vstring name, vstring shortName=vstring()) {
    _longNames.push(name);
    int* intTgt = reinterpret_cast<int*>(tgt);
    ALWAYS(_enumOptTargets.insert(name, intTgt));
    ALWAYS(_enumOptVals.insert(name, enumVals));
    if(shortName!="") {
      ALWAYS(_enumOptTargets.insert(shortName, intTgt));
      ALWAYS(_enumOptVals.insert(shortName, enumVals));
    }
  }

  bool readOption(vstring name, vstring value) const;
  bool readOptions(vstring str) const;

  void printOptionValue(vstring name, ostream& out);
  vstring getOptionStringValue(vstring optName);
  void printOptionValues(ostream& out, OptionsReader* defOpts=0, vstring linePrefix=vstring());

  static bool tryReadBool(vstring val, bool& tgt);

private:
  StringStack _longNames;

  DHMap<vstring,vstring*> _stringOptTargets;
  DHMap<vstring,int*> _intOptTargets;
  DHMap<vstring,unsigned*> _unsignedOptTargets;
  DHMap<vstring,float*> _floatOptTargets;
  DHMap<vstring,bool*> _boolOptTargets;
  DHMap<vstring,int*> _enumOptTargets;
  DHMap<vstring,EnumReaderBase> _enumOptVals;
};

}

#endif // __OptionsReader__
