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
    static void setBVCTFromDec(char n, BitVectorConstantType& res);
    
    
    static DArray<char> getHexArrayFromString(vstring& input);
    static BitVectorConstantType getBoolArrayFromVString(vstring& input);
    static bool setBVCTFromVString(vstring& input, BitVectorConstantType& result);
    static bool isOne(const BitVectorConstantType& arg);
    static bool isZero(const BitVectorConstantType& q);
    static bool getIndexOfLastOne(const BitVectorConstantType& arg, unsigned& result);

    static void specialMultBVCTByTen(BitVectorConstantType& arg1);
    static void multBVCTByTen(BitVectorConstantType& arg1);
    static bool addBVCTs(BitVectorConstantType& a1,const BitVectorConstantType& a2);
    static void subtractBVCTs(BitVectorConstantType& a1, const BitVectorConstantType& a2);
    static void inplaceShiftLeft(BitVectorConstantType& in, unsigned shiftByNum);
    static void inPlaceShiftRight(BitVectorConstantType& input, unsigned shiftByNum);
    static void inPlaceArithmeticShiftRight(BitVectorConstantType& input, unsigned shiftByNum);
    static void specialExtract(const BitVectorConstantType& arg1, unsigned indexLastOneArg2, BitVectorConstantType& result);
    static void printBVCT(const BitVectorConstantType& arg1);
  
    static void createHashmap();
    
    static void makeZeroBVCT(BitVectorConstantType& in);
    static BitVectorConstantType getZeroBVCT(unsigned size);
    static void makeOneBVCT(BitVectorConstantType& in);
    static BitVectorConstantType getOneBVCT(unsigned size);
    static void makeAllOnesBVCT(BitVectorConstantType& in);
    static BitVectorConstantType getAllOnesBVCT(unsigned size);
    
    static void bvneg(const BitVectorConstantType& arg, BitVectorConstantType& res);
    static void bvnot(const BitVectorConstantType& arg, BitVectorConstantType& res);
    static bool bvadd(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvxor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvnor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvxnor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvmul(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvurem(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvudiv(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvudiv_fast(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvsdiv(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvsrem(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvurem_fast(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvsmod(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvand(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvnand(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvshl(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvlshr(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvashr(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvsub(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void bvcomp(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void repeat(unsigned multBy, const BitVectorConstantType& arg , BitVectorConstantType& result);
    static void zero_extend(unsigned extendBy, const BitVectorConstantType& arg , BitVectorConstantType& result);
    static void sign_extend(unsigned extendBy, const BitVectorConstantType& arg , BitVectorConstantType& result);
    static void rotate_right(IntegerConstantType in, const BitVectorConstantType& arg , BitVectorConstantType& result);
    static void rotate_left(IntegerConstantType in, const BitVectorConstantType& arg , BitVectorConstantType& result);
    static void concat(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result);
    static void extract(unsigned upper, unsigned lower, const BitVectorConstantType& in, BitVectorConstantType& result);
    static void bvule(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result);
    static void bvuge(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result);
    static void bvugt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result);
    static void bvult(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result);
    static void bvslt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result);
    static void bvsle(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result);
    static void bvsgt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result);
    static void bvsge(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result);
    
    
    private:

   static DHMap<char, BitVectorConstantType> map;
    
    };  
}

#endif /* __BEE_VEE__ */

