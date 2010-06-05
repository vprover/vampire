/**
 * @file SpawningCM.hpp
 * Defines class SpawningCM.
 */

#ifndef __SpawningCM__
#define __SpawningCM__

#include "Forwards.hpp"

#include "Shell/Property.hpp"

#include "CASCMode.hpp"


namespace Shell
{
namespace CASC
{

class SpawningCM
: public CASCMode
{
public:
  SpawningCM(string executable);

protected:
  Property* getProperty() { return &_property; }

  bool runStrategy(Options& opt);

private:
  bool runStrategy(string strategy, unsigned ds);

  string _executable;
  string _inputFile;
  Property _property;
};

}
}

#endif // __SpawningCM__
