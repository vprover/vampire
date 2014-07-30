/**
 * @file OptionNameArray.cpp
 *
 * @author Giles
 * @since 30/07/14
 */

#include <cstring>

#include "Exception.hpp"
#include "OptionNameArray.hpp"
#include "Debug/Tracer.hpp"


std::ostream& operator<< (ostream& out, const Lib::OptionName& on ){
  CALL("operator<< (ostream&,const Lib::OptionNameArray::OptionName&)");

  out << "--" << on.longName << " (-" << on.shortName << ")" << endl;
  //TODO break description into 80 character chunks
  out << "\t" << on.description << endl;

  return out;
}

namespace Lib {

OptionNameArray::OptionNameArray (const OptionName array[],int len)
  : length(len),
    _array(array)
{
  CALL("OptionNameArray::OptionNameArray");

  for(int i=0;i<len;i++){
    _longArray[i] = _array[i].longName;
    _shortArray[i] = _array[i].shortName;
    #if VDEBUG
    if(i>0){
      ASS_REP2(strcmp(_longArray[i-1],_longArray[i]) <0, _longArray[i-1],_longArray[i]);
      ASS_REP2(strcmp(_shortArray[i-1],_shortArray[i]) <0, _shortArray[i-1],_shortArray[i]);
    }
    #endif
  }

} // OptionNameArray::OptionNameArray

/**
 * Find the index of a string in the long array. Throw a
 * ValueNotFoundException if it is not present.
 */
int OptionNameArray::findLong (const char* value) const
{
  CALL("OptionNameArray::findLong");

  int res=tryToFindLong(value);
  if(res==-1) {
    throw ValueNotFoundException();
  }
  return res;
} // OptionNameArray::findLong

/**
 * Find the index of a string in the long array. Return -1
 * if it is not present.
 */
int OptionNameArray::tryToFindLong(const char* value) const
{
  CALL("OptionNameArray::tryToFindLong");

  int from = 0;
  int to = length;
  while (from < to) {
    int mid = (from+to)/2;
    int comp = strcmp(_longArray[mid],value);
    if (comp < 0) {
      from = mid+1;
    }
    else if (comp == 0) {
      return mid;
    }
    else { // comp > 0
      to = mid;
    }
  }
  return -1;
} // OptionNameArray::tryToFindLong

/**
 * Find the index of a string in the short array. Throw a
 * ValueNotFoundException if it is not present.
 */
int OptionNameArray::findShort (const char* value) const
{
  CALL("OptionNameArray::findShort");

  int res=tryToFindShort(value);
  if(res==-1) {
    throw ValueNotFoundException();
  }
  return res;
} // OptionNameArray::findShort

/**
 * Find the index of a string in the short array. Return -1
 * if it is not present.
 */
int OptionNameArray::tryToFindShort(const char* value) const
{
  CALL("OptionNameArray::tryToFindShort");

  int from = 0;
  int to = length;
  while (from < to) {
    int mid = (from+to)/2;
    int comp = strcmp(_shortArray[mid],value);
    if (comp < 0) {
      from = mid+1;
    }
    else if (comp == 0) {
      return mid;
    }
    else { // comp > 0
      to = mid;
    }
  }
  return -1;
} // OptionNameArray::tryToFindShort

} // namespace Lib
