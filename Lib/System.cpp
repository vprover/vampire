/**
 * @file System.cpp
 * Wraps some system functions in a class. Introduce to cope with name conflicts with
 * Visual C++ functions.
 *
 * @since 31/03/2005 Torrevieja
 */

#ifdef _MSC_VER
#  include <Winsock2.h>
#  include <process.h>
#else 
#  include <unistd.h>
#endif

#include "System.hpp"

namespace Lib {

/**
 * Reimplements the system gethostname function.
 * @since 31/03/2005 Torrevieja
 */
void System::gethostname(char* hostname,int maxlength)
{
  ::gethostname(hostname,maxlength);
}

}
