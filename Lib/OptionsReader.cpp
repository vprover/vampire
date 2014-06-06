/**
 * @file OptionsReader.cpp
 * Implements class OptionsReader.
 */

#include <sstream>

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

  if(_stringOptTargets.find(name)) {
    *_stringOptTargets.get(name) = value;
    return true;
  }
  else if(_intOptTargets.find(name)) {
    return Int::stringToInt(value, *_intOptTargets.get(name));
  }
  else if(_unsignedOptTargets.find(name)) {
    unsigned& tgt = *_unsignedOptTargets.get(name);
    if(Int::stringToUnsignedInt(value, tgt)) {
      return true;
    }
    else if(value=="UINT_MAX" || value=="4294967295") {
      tgt = UINT_MAX;
      return true;
    }
    return false;
  }
  else if(_floatOptTargets.find(name)) {
    if(!Int::stringToFloat(value.c_str(), *_floatOptTargets.get(name))) {
      return false;
    }
    return true;
  }
  else if(_boolOptTargets.find(name)) {
    if(!tryReadBool(value, *_boolOptTargets.get(name))) {
      return false;
    }
    return true;
  }
  else if(_enumOptTargets.find(name)) {
    int* tgt = _enumOptTargets.get(name);
    const EnumReaderBase& rdr = _enumOptVals.get(name);
    if(!rdr.tryRead(value, *tgt)) {
      return false;
    }
    return true;
  }
  return false;
}

bool OptionsReader::readOptions(string str) const
{
  CALL("OptionsReader::readOptions");

  DHMap<string,string> optVals;
  if(!StringUtils::readEqualities(str.c_str(), ':', '=', optVals)) {
    return false;
  }

  DHMap<string,string>::Iterator oit(optVals);
  while(oit.hasNext()) {
    string name, val;
    oit.next(name, val);
    if(!readOption(name, val)) {
      return false;
    }
  }
  return true;
}

void OptionsReader::printOptionValue(string name, ostream& out)
{
  CALL("OptionsReader::printOptionValue");

  if(_stringOptTargets.find(name)) {
    out << *_stringOptTargets.get(name);
  }
  else if(_intOptTargets.find(name)) {
    out << *_intOptTargets.get(name);
  }
  else if(_unsignedOptTargets.find(name)) {
    out << *_unsignedOptTargets.get(name);
  }
  else if(_floatOptTargets.find(name)) {
    out << *_floatOptTargets.get(name);
  }
  else if(_boolOptTargets.find(name)) {
    out << ((*_boolOptTargets.get(name)) ? "on" : "off");
  }
  else if(_enumOptTargets.find(name)) {
    const EnumReaderBase& rdr = _enumOptVals.get(name);
    out << rdr.getValName(*_enumOptTargets.get(name));
  }
  else {
    ASSERTION_VIOLATION;
  }
}

string OptionsReader::getOptionStringValue(string optName)
{
  CALL("OptionsReader::getOptionStringValue");

  stringstream stm;
  printOptionValue(optName, stm);
  return stm.str();
}

void OptionsReader::printOptionValues(ostream& out, OptionsReader* defOpts, string linePrefix)
{
  CALL("OptionsReader::printOptionValues");

  StringStack::BottomFirstIterator nameIt(_longNames);
  while(nameIt.hasNext()) {
    string nm = nameIt.next();

    out << linePrefix << nm << ": ";
    printOptionValue(nm, out);
    if(defOpts) {
      if(getOptionStringValue(nm)==defOpts->getOptionStringValue(nm)) {
	out << " [default]";
      }
    }
    out << endl;
  }
}

}
