/**
 * @file System.hpp
 * Defines the class System that contains wrappers of some system functions
 * and methods that take care of the system stuff and don't fit anywhere
 * else (handling signals etc...)
 */

#ifndef __System__
#define __System__

#include <string>

bool outputAllowed();
bool inSpiderMode();
void reportSpiderFail();
void reportSpiderStatus(char status);

namespace Lib {

using namespace std;

class System {
public:
//  static void gethostname(char* hostname,int maxlength);
  static void setSignalHandlers();
  static string extractFileNameFromPath(string str);
};

}

#endif /* __System__ */
