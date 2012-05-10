/**
 * @file OptionsReader.hpp
 * Defines class OptionsReader.
 */

#ifndef __OptionsReader__
#define __OptionsReader__

#include "Forwards.hpp"

#include "DHMap.hpp"
#include "SmartPtr.hpp"

namespace Lib {

using namespace std;

class EnumReaderBase {
public:
  EnumReaderBase()
   : _vals(new DHMap<string,int>()), _names(new DHMap<int,string>())
  {
  }

  void addVal(string name, int val)
  {
    CALL("EnumReaderBase::addVal");
    ALWAYS(_vals->insert(name, val));
    ALWAYS(_names->insert(val, name));
  }
  bool tryRead(string name, int& val) const
  {
    CALL("EnumReaderBase::tryRead");
    return _vals->find(name, val);
  }
  string getValName(int val) const {
    return _names->get(val);
  }

  string toString() const {
    CALL("EnumReaderBase::toString");
    string res;
    DHMap<string,int>::Iterator valIt(*_vals);
    while(valIt.hasNext()) {
      string val = valIt.nextKey();
      res += val;
      if(valIt.hasNext()) {
	res+= ", ";
      }
    }
    return "["+res+"]";
  }

private:
  SmartPtr<DHMap<string,int> > _vals;
  SmartPtr<DHMap<int,string> > _names;
};

template<typename Enum>
class EnumReader : public EnumReaderBase {
public:
  void addVal(string name, Enum val)
  {
    CALL("EnumReader::addVal");

    EnumReaderBase::addVal(name, val);
  }
  bool tryRead(string name, Enum& val) const
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
  void registerIntOption(int* tgt, string name, string shortName=string()) {
    ALWAYS(_intOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_intOptTargets.insert(shortName, tgt));
    }
  }
  void registerUnsignedOption(unsigned* tgt, string name, string shortName=string()) {
    ALWAYS(_unsignedOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_unsignedOptTargets.insert(shortName, tgt));
    }
  }

  void registerFloatOption(float* tgt,string name, string shortName=string()) {
    ALWAYS(_floatOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_floatOptTargets.insert(shortName, tgt));
    }
  }

  void registerBoolOption(bool* tgt,string name, string shortName=string()) {
    ALWAYS(_boolOptTargets.insert(name, tgt));
    if(shortName!="") {
      ALWAYS(_boolOptTargets.insert(shortName, tgt));
    }
  }

  template<typename Enum>
  void registerEnumOption(Enum* tgt, EnumReaderBase enumVals, string name, string shortName=string()) {
    int* intTgt = reinterpret_cast<int*>(tgt);
    ALWAYS(_enumOptTargets.insert(name, intTgt));
    ALWAYS(_enumOptVals.insert(name, enumVals));
    if(shortName!="") {
      ALWAYS(_enumOptTargets.insert(shortName, intTgt));
      ALWAYS(_enumOptVals.insert(shortName, enumVals));
    }
  }

  bool readOption(string name, string value) const;
  bool readOptions(string str) const;

  void printOptionValue(string name, ostream& out);

  static bool tryReadBool(string val, bool& tgt);

private:
  DHMap<string,int*> _intOptTargets;
  DHMap<string,unsigned*> _unsignedOptTargets;
  DHMap<string,float*> _floatOptTargets;
  DHMap<string,bool*> _boolOptTargets;
  DHMap<string,int*> _enumOptTargets;
  DHMap<string,EnumReaderBase> _enumOptVals;
};

}

#endif // __OptionsReader__
