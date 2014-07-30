/**
 * @file OptionNameArray.hpp
 *
 * @since 21/04/2005 Manchester
 */

#include <string>

using namespace std;

namespace Lib {

/**
* Store information about an Option
* i.e. long and short names, description and whether it is experimental
*
* Note: All components are required, including shortName
*
* @author Giles
*/
struct OptionName{
  OptionName(const char* l, const char* s, const char* d, const bool e) :
     longName(l), shortName(s), description(d), experimental(e) {}
  const char* longName;
  const char* shortName;
  const char* description;
  const bool experimental;

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
  const OptionName operator[] (int i) const { return _array[i]; }
  /** The length of the array */
  const int length;
private:
  /** Long array */
  const char** _longArray;
  /** Short array */
  const char** _shortArray;
  /** Actual array */
  const OptionName* _array;
}; // class NameArray

}

std::ostream& operator<< (ostream& out, const Lib::OptionName& on );
