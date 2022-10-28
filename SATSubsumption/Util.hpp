#ifndef SATSUBSUMPTION_UTIL_HPP
#define SATSUBSUMPTION_UTIL_HPP

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"

bool checkClauseEquality(Kernel::Literal const* const lits1[], unsigned len1, Kernel::Literal const* const lits2[], unsigned len2);
bool checkClauseEquality(Kernel::Clause* const cl1, Kernel::Clause* const cl2);

#endif /* !SATSUBSUMPTION_UTIL_HPP */
