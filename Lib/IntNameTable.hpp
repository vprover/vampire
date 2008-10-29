/**
 * @file IntNameTable.hpp
 *
 * Defines the class IntNameTable for a table of names, 
 * where insert returns an integer.
 *
 * @since 13/05/2000 flight Manchester-Atlanta, made from NameTable
 * @since 02/12/2003 Manchester, change to use strings instead of char*
 * @since 08/04/2006 Bellevue, changed to use maps
 */

#ifndef __IntNameTable__
#define __IntNameTable__

#include <string>

#include "Array.hpp"
#include "Map.hpp"

using namespace std;

namespace Lib {

class IntNameTable 
{
 public:
  IntNameTable();
  int insert(const string& str);
  /** return name number n */
  inline string operator[] (int n) const { return _names[n]; }
//   int numberOfSymbols();

 private:
  Map <string,int,Hash> _map;
  Array<string> _names;
  int _nextNumber;
}; // class NameTable

}

#endif
