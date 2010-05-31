/**
 * @file StringUtils.hpp
 * Defines class StringUtils.
 */

#ifndef __StringUtils__
#define __StringUtils__

#include <string>

namespace Lib {

using namespace std;

class StringUtils {
public:
  static string replaceChar(string str, char src, char target);
};

}

#endif // __StringUtils__
