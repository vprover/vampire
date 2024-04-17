/*
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file UPCoP.hpp
 * Defines MainLoop object for UPCoP
 */

#include "Kernel/MainLoop.hpp"

class UPCoP: public Kernel::MainLoop {
public:
  UPCoP(Kernel::Problem &prb, const Shell::Options &opt)
    : Kernel::MainLoop(prb, opt) {}

protected:
  void init() override {};
  Kernel::MainLoopResult runImpl() override;
};
