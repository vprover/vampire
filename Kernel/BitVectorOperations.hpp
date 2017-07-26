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
    using namespace std;
    using namespace Lib;
    
    //  temporary workaround before moving BVCT to its appropriate place
    /*class BitVectorConstantType;
    class BitVectorConstantType{
       
    
    typedef DArray<bool> BinArray;
    public: // for some reason have to put the constructor here
        //explicit BitVectorConstantType(const vstring& size, const vstring& numberToRepresent);
        explicit BitVectorConstantType(const DArray<bool> n);
        BitVectorConstantType(){};
    vstring toString() const;

    unsigned size() const {return binArray.size();}
    unsigned getSort() const {
         //return sortB; 
         return env.sorts->addBitVectorSort(binArray.size()); // this should probabyl be changed to getBitVectorSort
    } 
    void setBinArray(DArray<bool> setTo)
    {
        binArray.initFromArray(setTo.size(),setTo);
    }
    
    DArray<bool> getBinArray() const{
        return binArray;
    }
    
    
private: 
    
   // NumberToRepresent _numberToRepresent;
    unsigned sortB;
    BinArray binArray;
};*/
    
    class BitVectorOperations{
    public:
    static IntegerConstantType test();    
    static vstring boolArraytoString(const DArray<bool>& in);
    static BitVectorConstantType getBVCTFromVString(vstring& numberToRepresent, unsigned size);
    static BitVectorConstantType padBVCT(BitVectorConstantType input, unsigned size);
    static void printBoolArrayContent(DArray<bool> array);
    static BitVectorConstantType getBVCTFromDec(char n);

    static bool addBinArrays(const DArray<bool>& a1, const DArray<bool>& a2, DArray<bool>& result);
    static DArray<bool> shiftLeft(DArray<bool> input, unsigned shiftByNum);

    static BitVectorConstantType multBVCTs(BitVectorConstantType a1, BitVectorConstantType a2);
    static BitVectorConstantType fitBVCTIntoBits(BitVectorConstantType input, unsigned size);
    static BitVectorConstantType truncate(BitVectorConstantType input, unsigned size);
    };  
}

#endif /* __BEE_VEE__ */

