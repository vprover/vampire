/**
 * @file System.hpp
 * Defines the class System that contains wrappers of some system functions
 * and methods that take care of the system stuff and don't fit anywhere
 * else (handling signals etc...)
 */

#ifndef __System__
#define __System__

#include <string>

#include "Forwards.hpp"

#include "Array.hpp"
#include "List.hpp"
#include "Portability.hpp"

bool outputAllowed();
bool inSpiderMode();
void reportSpiderFail();
void reportSpiderStatus(char status);

namespace Lib {

using namespace std;

typedef void (*SignalHandler)(int);

class System {
public:
//  static void gethostname(char* hostname,int maxlength);
  static void setSignalHandlers();
  static string extractFileNameFromPath(string str);

  static void ignoreSIGINT() { s_shouldIgnoreSIGINT=true; }
  static void heedSIGINT() { s_shouldIgnoreSIGINT=false; }
  static bool shouldIgnoreSIGINT() { return s_shouldIgnoreSIGINT; }

  static void addInitializationHandler(VoidFunc proc, unsigned priority=0);
  static void onInitialization();

  static void addTerminationHandler(VoidFunc proc, unsigned priority=0);
  static void onTermination();
  static void terminateImmediately(int resultStatus) __attribute__((noreturn));

  static void registerForSIGHUPOnParentDeath();

  /**
   * Return the size of system physical memory in bytes
   */
  static long long getSystemMemory();

  /**
   * Return number of CPU cores
   */
  static unsigned getNumberOfCores();

  static bool fileExists(string fname);

private:

  static ZIArray<List<VoidFunc>*>& initializationHandlersArray();

  /**
   * True if the @b onInitialization() function was already called
   *
   * If this variable is true, the @b addInitializationHandler()
   * function will immediately call the function that is supposed
   * to be an initialization handler, rather than put it into the
   * handler list. This is done because the functions in the handler
   * list were already called at that point.
   */
  static bool s_initialized;

  /**
   * Lists of functions that will be called before Vampire terminates
   *
   * Functions in lists with lower numbers will be called first.
   */
  static ZIArray<List<VoidFunc>*> s_terminationHandlers;

  static bool s_shouldIgnoreSIGINT;
};

}

#endif /* __System__ */
