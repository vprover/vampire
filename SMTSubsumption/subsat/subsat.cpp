#include "subsat.hpp"

#include <iostream>

using namespace SMTSubsumption;

#ifdef SUBSAT_STANDALONE
int main()
{
    std::cout << "hello" << std::endl;
    Solver s;
    return 0;
}
#endif
