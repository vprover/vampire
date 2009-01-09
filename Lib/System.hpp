/**
 * @file System.hpp
 * Defines the class System that contains wrappers of some system functions
 * and methods that take care of the system stuff and don't fit anywhere
 * else (handling signals etc...)
 */


namespace Lib {

class System {
public:
  static void gethostname(char* hostname,int maxlength);
  static void setSignalHandlers();

};

}
