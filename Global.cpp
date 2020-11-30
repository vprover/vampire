/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Global.cpp
 * Defines all global (static) members that must be initialised
 * in a fixed order. Created due to the usual C++ problems with the
 * order of initialisation of static members.
 *
 * @since 11/12/2003 Manchester
 */

#include "Lib/Array.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/System.hpp"

// From here the order does matter

Lib::ZIArray<Lib::List<VoidFunc>*> Lib::System::s_terminationHandlers(2);

Lib::Environment Lib::env;


struct __Lib_System_Init_Invoker
{
  __Lib_System_Init_Invoker()
  {
    Lib::System::onInitialization();
  }
};

__Lib_System_Init_Invoker __Lib_System_Init_Invoker_obj;

