/**
 * @file System.hpp
 * Defines the class System wrapping some system functions. 
 * Introduce to cope with name conflicts with
 * Visual C++ functions.
 *
 * @since 31/03/2005 Torrevieja
 */

namespace Lib {

class System {
public:
  static void gethostname(char* hostname,int maxlength);
};

}
