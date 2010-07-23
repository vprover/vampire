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
  /**
   * Run a slice correponding to the options.
   * Return true iff the proof or satisfiability was found
   */
  virtual bool runSlice(Options& opt);

private:
  string _executable;
  string _inputFile;
};

}
}

#endif // __SpawningCM__
