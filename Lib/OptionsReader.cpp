/**
 * @file OptionsReader.cpp
 * Implements class OptionsReader.
 */

#include "Int.hpp"
#include "StringUtils.hpp"

#include "OptionsReader.hpp"

namespace Lib
{

bool OptionsReader::tryReadBool(string val, bool& tgt)
{
  CALL("OptionsReader::tryReadBool");

  if(val=="on") {
    tgt = true;
    return true;
  }
  else if(val=="off") {
    tgt = false;
    return true;
  }
  return false;
}

bool OptionsReader::readOption(string name, string value) const
{
  CALL("OptionsReader::readOption");

  if(_intOptTargets.find(name)) {
    return Int::stringToInt(value, *_intOptTargets.get(name));
  }
  else if(_unsignedOptTargets.find(name)) {
    unsigned& tgt = *_unsignedOptTargets.get(name);
    if(Int::stringToUnsignedInt(value, tgt)) {
      return true;
    }
    else if(value=="UINT_MAX") {
      tgt = UINT_MAX;
      return true;
    }
    return false;
  }
  else if(_floatOptTargets.find(name)) {
    return Int::stringToFloat(value.c_str(), *_floatOptTargets.get(name));
  }
  else if(_boolOptTargets.find(name)) {
    return tryReadBool(value, *_boolOptTargets.get(name));
  }
  else if(_enumOptTargets.find(name)) {
    int* tgt = _enumOptTargets.get(name);
    const EnumReaderBase& rdr = _enumOptVals.get(name);
    if(!rdr.tryRead(value, *tgt)) {
      LOG("or_fail","bad enum value: "<<name<<" = "<<value);
      LOG("or_fail","possible values: "<<rdr.toString());
      return false;
    }
    return true;
  }
  LOG("or_fail","unknown option name: "<<name<<" = "<<value);
  return false;
}

bool OptionsReader::readOptions(string str) const
{
  CALL("OptionsReader::readOptions");

  DHMap<string,string> optVals;
  StringUtils::readEqualities(str.c_str(), ':', '=', optVals);

  DHMap<string,string>::Iterator oit(optVals);
  while(oit.hasNext()) {
    string name, val;
    oit.next(name, val);
    if(!readOption(name, val)) {
      LOG("or_fail","could not set option: "<<name<<" = "<<val);
      return false;
    }
    LOG("or_set","have set option: "<<name<<" = "<<val);
  }
  return true;
}


}
