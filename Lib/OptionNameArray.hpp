/**
 * @file OptionNameArray.hpp
 *
 * @since 21/04/2005 Manchester
 */

#include <string>
#include "Lib/Stack.hpp"
#include "Shell/Options.hpp"
#include "Allocator.hpp"
#include "NameArray.hpp"

using namespace std;
using namespace Shell;

namespace Lib {

/**
 * Allows us to give a variable number of option values
 * This is a bit of a hack, and a nicer solution would be to have a variable argument
 * constructor. But this is simpler, in some senses.
 *
 * Note: It may be necessary to add a new constructor
 *
 * @author Giles
 * @since 30/07/14
 */
struct OptionValues{
  OptionValues(const char* s1, const char* s2) : _len(2)
    { makeArray(); _array[0]=s1;_array[1]=s2; } 
  OptionValues(const char* s1, const char* s2, const char* s3) : _len(3) 
    { makeArray();_array[0]=s1;_array[1]=s2; _array[2]=s3; }
  OptionValues(const char* s1, const char* s2, const char* s3, const char* s4) : _len(4) 
    { makeArray();_array[0]=s1;_array[1]=s2; _array[2]=s3; _array[3]=s4; }
  OptionValues(const char* s1, const char* s2, const char* s3, const char* s4, const char* s5) : _len(5) 
    { makeArray();_array[0]=s1;_array[1]=s2; _array[2]=s3; _array[3]=s4; _array[4]=s5; }
  OptionValues(const char* s1, const char* s2, const char* s3, const char* s4, const char* s5,
               const char* s6) : _len(6)
    { makeArray();_array[0]=s1;_array[1]=s2; _array[2]=s3; _array[3]=s4; _array[4]=s5; _array[5]=s6; }
  OptionValues(const char* s1, const char* s2, const char* s3, const char* s4, const char* s5,
               const char* s6, const char* s7) : _len(7)
    { makeArray();_array[0]=s1;_array[1]=s2;_array[2]=s3;_array[3]=s4;_array[4]=s5;_array[5]=s6;_array[6]=s7; }
  OptionValues(const char* s1, const char* s2, const char* s3, const char* s4, const char* s5,
               const char* s6, const char* s7, const char* s8) : _len(8)
    { makeArray();_array[0]=s1;_array[1]=s2; _array[2]=s3; _array[3]=s4; _array[4]=s5; _array[5]=s6;
      _array[6]=s7; _array[7]=s8; }
  OptionValues(const char* s1, const char* s2, const char* s3, const char* s4, const char* s5,
               const char* s6, const char* s7, const char* s8, const char* s9) : _len(9)
    { makeArray();_array[0]=s1;_array[1]=s2; _array[2]=s3; _array[3]=s4; _array[4]=s5; _array[5]=s6;
      _array[6]=s7; _array[7]=s8;_array[8]=s9; }
  OptionValues(const char* s1, const char* s2, const char* s3, const char* s4, const char* s5,
               const char* s6,const char* s7,const char* s8,const char* s9,const char* s10) : _len(10)
    { makeArray();_array[0]=s1;_array[1]=s2; _array[2]=s3; _array[3]=s4; _array[4]=s5; _array[5]=s6;
      _array[6]=s7; _array[7]=s8; _array[8]=s9; _array[9]=s10; }

  // For mode - lots of modes!
  OptionValues(const char* s1, const char* s2, const char* s3, const char* s4, const char* s5,
               const char* s6, const char* s7, const char* s8, const char* s9, const char* s10,
               const char* s11, const char* s12, const char* s13, const char* s14, const char* s15,
               const char* s16, const char* s17, const char* s18, const char* s19) : _len(19)
    { makeArray();_array[0]=s1;_array[1]=s2;_array[2]=s3;_array[3]=s4;_array[4]=s5;_array[5]=s6;_array[6]=s7;
      _array[7]=s8;_array[8]=s9; _array[9]=s10; _array[10]=s11; _array[11]=s12; _array[12]=s13;
      _array[13]=s14;_array[14]=s15; _array[15]=s16; _array[16]=s17; _array[17]=s18; _array[18]=s19;
    }

  const char**  _array;
  int _len;
  private:
    OptionValues() : _len(0) {};
    void makeArray(){ _array = new const char*[_len]; }
};


/**
 * Store information about an Option
 * i.e. long and short names, description and whether it is experimental
 *
 * @author Giles
 */
struct OptionName {

  OptionName(const char* l, const char* s, const char* d, const bool e,
             const char* def = 0) :
               longName(l), shortName(s), description(d),experimental(e),default_value(def) 
  { 
    tags.push(Options::GLOBAL_TAG);
    names=0;
  }

  OptionName(const char* l, const char* s, Options::OptionTag t, const char* d, const bool e,
             const char* def = 0) : 
               longName(l), shortName(s), description(d),experimental(e),default_value(def) 
  { 
    tags.push(t);
    names=0;
  }

  OptionName(const char* l, const char* s, Options::OptionTag t, const char* d, const bool e,
             const char* def, OptionValues choices) : 
               longName(l), shortName(s), description(d),experimental(e), 
               default_value(def) 
  { 
    tags[0] = t;
    names = new NameArray(choices._array,choices._len);
    ASS(names->tryToFind(default_value) != -1);
  }

  void addTag(Options::OptionTag t){
    tags.push(t);
  }

  ~OptionName(){
    if(names){ delete names;}
  }

  const char* longName;
  const char* shortName;
  Stack<Options::OptionTag> tags;
  const char* description;
  const bool experimental;
  const char* default_value;
  NameArray* names; 
};


/**
 * An container for OptionNames
 * Stores two arrays ordered by long and short names respectively
 * Stores one array of OptionName objects
 *
 * @author Giles
 * @since 30/07/14
 */
class OptionNameArray {
public:

  OptionNameArray(const OptionName array[],int length);
  /** Find index based on long name **/
  int findLong(const char* value) const;
  int tryToFindLong(const char* value) const;
  /** Find index based on short name **/
  int findShort(const char* value) const;
  int tryToFindShort(const char* value) const;
  /** Return i-th element of the array */
  const OptionName& operator[] (int i) const { return _array[i]; }
  /** The length of the array */
  const int length;
private:
  /** Long array */
  const char** _longArray;
  /** Short array */
  const char** _shortArray;
  int first_short[26];
  /** Actual array */
  const OptionName* _array;
}; // class NameArray

}

std::ostream& operator<< (ostream& out, const Lib::OptionName& on );
