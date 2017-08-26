/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   BitVectorOperations.hpp
 * Author: dam
 *
 * Created on July 19, 2017, 8:51 AM
 */

#ifndef __BEE_VEE__
#define __BEE_VEE__
#include <iostream>
#include "Debug/Assertion.hpp"
#include "Lib/DArray.hpp"
#include "Sorts.hpp"
#include "Theory.hpp"
#include "Lib/Environment.hpp"

namespace Kernel {
    
    class BitVectorOperations{
    
    public:
     
    static vstring boolArraytoString(const DArray<bool>& in);
    static BitVectorConstantType getBVCTFromVString(vstring& numberToRepresent, unsigned size);
    static BitVectorConstantType getBVCTFromDec(char n,unsigned size);
    static DArray<char> getHexArrayFromString(vstring& input);
    static BitVectorConstantType getBoolArrayFromVString(vstring& input);
    
    static void multBVCTByTen(BitVectorConstantType& arg1);
    static bool addBVCTs(BitVectorConstantType& a1,const BitVectorConstantType& a2);
    static void inplaceShiftLeft(BitVectorConstantType& in, unsigned shiftByNum);

    static void createHashmap();
    static void printHashmap();  
    
    static void printBoolArrayContent(DArray<bool> array);
    };  
}

#endif /* __BEE_VEE__ */

