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

  out << "--" << on.longName;
  if(strcmp(on.shortName,"")!=0){ out << " (-"<<on.shortName<<")"; }
  out << endl; 

  if(strcmp(on.description,"")!=0){
    // Break a the description into lines where there have been at least 70 characters
    // on the line at the next space
    out << "\t";
    int count=0;
    for(const char* p = on.description;*p;p++){
      out << *p; 
      count++;
      if(count>70 && *p==' '){
        out << endl << '\t';
        count=0;
      }
      if(*p=='\n'){ count=0; out << '\t'; }
    }
    out << endl;
  }
  else{ out << "\tno description provided!" << endl; }

  if(on.names){
    out << "\tvalues: ";
    for(int i=0;i<(*on.names).length;i++){
      if(i==0){
        out << (*on.names)[i];
      }
      else{
        out << ","<<(*on.names)[i];
      }
    }
    out << endl;
  }
  if(on.default_value){
    out << "\tdefault: " << on.default_value << endl;
  }

  return out;
}

namespace Lib {

OptionNameArray::OptionNameArray (const OptionName array[],int len)
  : length(len),
    _array(array)
{
  CALL("OptionNameArray::OptionNameArray");

  // create memory for long and short array
  _longArray = (const char**) ALLOC_KNOWN(sizeof(char*)*len,"OptionNameArray<>");
  _shortArray = (const char**) ALLOC_KNOWN(sizeof(char*)*len,"OptionNameArray<>");
  
  char last_firsts = -1;
  for(int i=0;i<len;i++){
    _longArray[i] = _array[i].longName;
    _shortArray[i] = _array[i].shortName;
    char firsts = _array[i].shortName[0];
    #if VDEBUG
    ASS_REP(!firsts || (firsts >= 'a' && firsts <= 'z'),_shortArray[i]);
    if(i>0){
      ASS_REP2(strcmp(_longArray[i-1],_longArray[i]) <0, _longArray[i-1],_longArray[i]);
      ASS(!firsts || (firsts >= last_firsts));
      if(firsts){
        for(int j=i-1;j>0;j--){
          ASS_REP2(strcmp(_shortArray[j],_shortArray[i])!=0,_shortArray[j],_shortArray[i]);
        }
      }
    }
    #endif
    if(firsts && last_firsts != firsts){
      first_short[firsts-'a']=i;
      last_firsts = firsts;
    }
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

  int start = first_short[value[0]-'a'];
  for(int i=start;i<length;i++){
    if(strcmp(_shortArray[i],value) == 0){
      return i;
    }
  }
  return -1;
} // OptionNameArray::tryToFindShort

} // namespace Lib
