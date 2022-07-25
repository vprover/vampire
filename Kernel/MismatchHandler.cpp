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
 * @file MismatchHandler.cpp
 * Defines class MismatchHandler.
 *
 */

#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"
#include "Lib/BiMap.hpp"

#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"

#include "MismatchHandler.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

namespace Kernel
{

// bool UWAMismatchHandler::handle(TermList t1, unsigned index1, TermList t2, unsigned index2, VSpecVarToTermMap* termMap)
// {
//   CALL("UWAMismatchHandler::handle");
//
//   ASS(!t1.isSpecialVar()  && !t2.isSpecialVar());
//   if(t1.isOrdinaryVar() || t2.isOrdinaryVar()) return false;
//
//   if(checkUWA(t1,t2)){
//     Term* tm1 = t1.isVSpecialVar() ? termMap->get(t1.var()) : t1.term();
//     Term* tm2 = t2.isVSpecialVar() ? termMap->get(t2.var()) : t2.term();
//
//     if(tm1 == tm2 && tm1->shared() && tm1->ground()){ return true; }
//    
//     TermList tt1 = TermList(tm1);
//     TermList tt2 = TermList(tm2);
//
//     RobSubstitution::TermSpec t1spec = RobSubstitution::TermSpec(tt1, index1);
//     RobSubstitution::TermSpec t2spec = RobSubstitution::TermSpec(tt2, index2);
//
//     if(t1spec.sameTermContent(t2spec)){ return true; }
//
//     //cout << "Introducing constraint: <" + tt1.toString() << " , " << tt2.toString() << ">" << endl; 
//
//     return introduceConstraint(tt1,index1,tt2,index2);
//   }
//   return false;
// }
//
// bool UWAMismatchHandler::checkUWA(TermList t1, TermList t2)
// {
//   CALL("UWAMismatchHandler::checkUWA");
//
//   static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();
//   // handler should never be called if UWA is off
//   ASS(opt != Shell::Options::UnificationWithAbstraction::OFF);
//
//   if((t1.isVSpecialVar() && !t2.isVSpecialVar()) || 
//      (t2.isVSpecialVar() && !t1.isVSpecialVar())  ){
//     // At the moment we assume that there are only two settings for UWA
//     // both terms must be interpreted, or at least one term be interpreted.
//     // If statement below checks for the case where both terms must be interpreted
//     // but only one of the terms passed to the handler is an interpreted one.
//     if(opt != Shell::Options::UnificationWithAbstraction::ONE_INTERP){
//       return false;
//     }
//     return true;
//   }
//
//   ASS(t1.isVSpecialVar() && t2.isVSpecialVar());
//   return true;
// }
//
// bool UWAMismatchHandler::introduceConstraint(TermList t1,unsigned index1, TermList t2,unsigned index2)
// {
//   CALL("UWAMismatchHandler::introduceConstraint");
//
//   auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
//   constraints.push(constraint);
//   return true;
// }
//
// bool HOMismatchHandler::handle(TermList t1, unsigned index1, TermList t2, unsigned index2, VSpecVarToTermMap* termMap)
// {
//   CALL("HOMismatchHandler::handle");
//
//   if(!t1.isVSpecialVar() && !t2.isVSpecialVar()){
//     return false;
//   }
//
//   Term* tm1 = termMap->get(t1.var());
//   Term* tm2 = termMap->get(t2.var());
//
//   if(tm1 == tm2 && tm1->shared() && tm1->ground()){ return true; }
//  
//   TermList tt1 = TermList(tm1);
//   TermList tt2 = TermList(tm2);
//
//   RobSubstitution::TermSpec t1spec = RobSubstitution::TermSpec(tt1, index1);
//   RobSubstitution::TermSpec t2spec = RobSubstitution::TermSpec(tt2, index2);
//
//   if(t1spec.sameTermContent(t2spec)){ return true; }
//
//   return introduceConstraint(tt1,index1,tt2,index2);
// }
//
// bool HOMismatchHandler::introduceConstraint(TermList t1, unsigned index1, TermList t2, unsigned index2)
// {
//   CALL("HOMismatchHandler::introduceConstraint");
//
//   auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
//   constraints.push(constraint);
//   return true; 
// }

}
