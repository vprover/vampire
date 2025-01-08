/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include <iostream>
#include "Kernel/Theory.hpp"
#include "Lib/List.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

TEST_FUN(list_1)
{
  IntList* lst = 0;

  IntList::push(0, lst);
  IntList::push(1, lst);

  IntList::DelIterator dit(lst);
  ALWAYS(dit.hasNext());
  ALWAYS(dit.next()==1);
  dit.del();
  ASS_EQ(lst->head(), 0);
  ASS_ALLOC_TYPE(lst, "List");
}

TEST_FUN(to_string)
{
  for (std::string str : { 
      "1111111111111111111111111111111111111111111",
      "-1111111111111111111111111111111111111111111",
      "1111111189123097123890102111111111111111111",
      }) {
    ASS_EQ(Output::toString(IntegerConstantType::parse(str).unwrap()), str);
  }
}

TEST_FUN(parse_real)
{
  ASS_EQ(RealConstantType::parse("0.123E20"), 
         RealConstantType::parse("12300000000000000000"));
  ASS_EQ(RealConstantType::parse("0.123e20"), 
         RealConstantType::parse("12300000000000000000"));
  ASS_EQ(RealConstantType::parse("0.123E-8"), 
         RealConstantType::parse("0.00000000123"));
  ASS_EQ(RealConstantType::parse("0.123e-8"), 
         RealConstantType::parse("0.00000000123"));
}
