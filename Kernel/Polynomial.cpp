#include "Kernel/Polynomial.hpp"


#define INSTANTIATE_STATIC(value) \
  template<> decltype(value) value = decltype(value)();

#define INSTANTIATE_STATICS(Integer) \
  INSTANTIATE_STATIC(Kernel::Monom  <Kernel::NumTraits<Kernel::Integer ## ConstantType>>::monoms  ) \
  INSTANTIATE_STATIC(Kernel::Polynom<Kernel::NumTraits<Kernel::Integer ## ConstantType>>::polynoms)

INSTANTIATE_STATICS(Integer)
INSTANTIATE_STATICS(Rational)
INSTANTIATE_STATICS(Real)
