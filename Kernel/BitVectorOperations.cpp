
/*
 * File BitVectorOperations.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file BitVectorOperations.cpp
 * Implements class BitVectorOperations.
 * @since 19/07/2017 
 * @author David Damestani
 */

#include "BitVectorOperations.hpp"


namespace Kernel{

DHMap<char, BitVectorConstantType> BitVectorOperations::map;

void BitVectorOperations::createHashmap()
{
    bool zero[] = {false}; // 0 
    bool one[] = {true}; // 1
    bool two[] = {false, true}; // 01
    bool three[] = {true, true}; // 11
    bool four[] = {false, false, true}; // 001
    bool five[] = {true, false, true}; // 101
    bool six[] = {false, true, true}; // 011
    bool seven[] = {true, true, true}; // 111
    bool eight[] = {false, false, false, true}; // 0001
    bool nine[] = {true, false, false, true}; // 1001
    bool ten[] = {false, true, false, true}; // 0101
    bool eleven[] = {true, true, false, true}; // 1101
    bool twelve[] = {false, false, true, true}; // 0011
    bool thirteen[] = {true, false, true, true}; // 1011
    bool fourteen[] = {false, true, true, true}; // 0111
    bool fifteen[] = {true, true, true, true}; // 1111

    // zero
    DArray<bool> toAdd;
    toAdd.initFromArray(1,zero);
    BitVectorConstantType bvToAdd(toAdd);
    map.insert('0',bvToAdd);
    
    // one
    toAdd.initFromArray(1,one);
    bvToAdd.setBinArray(toAdd);
    map.insert('1',bvToAdd);
    
    //two
    toAdd.initFromArray(2,two);
    bvToAdd.setBinArray(toAdd);
    map.insert('2',bvToAdd);
    
    //three
    toAdd.initFromArray(2,three);
    bvToAdd.setBinArray(toAdd);
    map.insert('3',bvToAdd);
    
    //four
    toAdd.initFromArray(3,four);
    bvToAdd.setBinArray(toAdd);
    map.insert('4',bvToAdd);
    
    //five
    toAdd.initFromArray(3,five);
    bvToAdd.setBinArray(toAdd);
    map.insert('5',bvToAdd);
    
    //six
    toAdd.initFromArray(3,six);
    bvToAdd.setBinArray(toAdd);
    map.insert('6',bvToAdd);
    
    //seven
    toAdd.initFromArray(3,seven);
    bvToAdd.setBinArray(toAdd);
    map.insert('7',bvToAdd);
    
    //eight
    toAdd.initFromArray(4,eight);
    bvToAdd.setBinArray(toAdd);
    map.insert('8',bvToAdd);
    
    //nine
    toAdd.initFromArray(4,nine);
    bvToAdd.setBinArray(toAdd);
    map.insert('9',bvToAdd);
    
    // 10 = 'a'
    toAdd.initFromArray(4,ten);
    bvToAdd.setBinArray(toAdd);
    map.insert('a',bvToAdd);
    
    // 10 = 'A'
    map.insert('A',bvToAdd);
    
    // 11 = 'b'
    toAdd.initFromArray(4,eleven);
    bvToAdd.setBinArray(toAdd);
    map.insert('b',bvToAdd);
    
    // 11 = 'B'
    map.insert('B',bvToAdd);
    
    // 12 = 'c'
    toAdd.initFromArray(4,twelve);
    bvToAdd.setBinArray(toAdd);
    map.insert('c',bvToAdd);
    
    // 12 = 'C'
    map.insert('C',bvToAdd);
    
    // 13 = 'd'
    toAdd.initFromArray(4,thirteen);
    bvToAdd.setBinArray(toAdd);
    map.insert('d',bvToAdd);
    
    // 13 = 'D'
    map.insert('D',bvToAdd);
    
    // 14 = 'e'
    toAdd.initFromArray(4,fourteen);
    bvToAdd.setBinArray(toAdd);
    map.insert('e',bvToAdd);
    
    // 14 = 'E'
    map.insert('E',bvToAdd);
    
    // 15 = 'f'
    toAdd.initFromArray(4,fifteen);
    bvToAdd.setBinArray(toAdd);
    map.insert('f',bvToAdd);
    
    // 15 = 'F'
    map.insert('F',bvToAdd);
    
}

bool BitVectorOperations::getIndexOfLastOne(const BitVectorConstantType& arg, unsigned& result)
{
    bool containsOne = false;
    for (unsigned i = 0; i<arg.size(); ++i){
        if (arg.getValueAt(i)==true){
            containsOne = true;
            result=i;
        }
    }
    return containsOne;
}

bool BitVectorOperations::isOne(const BitVectorConstantType& arg)
{
    if (!arg.getValueAt(0))
        return false;
    for (unsigned i = 1; i < arg.size(); ++i){
        if (arg.getValueAt(i)){
            return false;
        }
    }
    return true;
}

bool BitVectorOperations::isZero(const BitVectorConstantType& q)
{
    for (unsigned i = 0 ; i <q.size();++i){
        if (q.getValueAt(i))
            return false;
        }
    return true;
}

void BitVectorOperations::setBVCTFromDec(char n, BitVectorConstantType& res)
{
    ASS(res.size()>0);
    
    BitVectorConstantType bvct = map.get(n);
    unsigned i = 0 ;
    
    for (; i < res.size() && i<bvct.size(); ++ i){
        res.setValueAt(i,bvct.getValueAt(i));
    }
    for ( ; i < res.size(); ++ i){
        res.setValueAt(i,false);
    }
}

    
vstring BitVectorOperations::boolArraytoString(const DArray<bool>& in)
{
    CALL("BitVectorOperations::boolArraytoString(DArray<bool>&)");
    vstring out = "";
    for (unsigned i = 0; i < in.size(); ++ i)
    {
        if (in[i]) {
          out = "1" + out;
        } else {
          out = "0" + out;
        }
    }
    return out;
}


// set a BVCT from a string like this 010010 and return false if it contains anything but zero or one
bool BitVectorOperations::setBVCTFromVString(vstring& input, BitVectorConstantType& result)
 {
    CALL("BitVectorOperations::setBVCTFromVString(vstring&,BitVectorConstantType&)");
    for (unsigned j = 0, i = input.length()-1; j<input.length();--i, ++j){
        if (input.at(j) == '0')
            result.setValueAt(i,false);
        else if (input.at(j) == '1')
            result.setValueAt(i,true);
        else
            return false;
    }
    return true;
 }

BitVectorConstantType BitVectorOperations::getBVCTFromVString(vstring& numberToRepresent, unsigned size)
{
    CALL("BitVectorOperations::getBVCTFromVString(vstring&,unsigned)");
    char c = numberToRepresent[0];
    BitVectorConstantType currentDec(size);
    setBVCTFromDec(c,currentDec);
    BitVectorConstantType sum(currentDec.getBinArray());
    
    for(unsigned i = 1; i<numberToRepresent.length(); i++) {
        multBVCTByTen(sum);
        c = numberToRepresent[i]; 
        setBVCTFromDec(c,currentDec);
        addBVCTs(sum,currentDec);
    }
    return sum;
} 
 bool BitVectorOperations::addBVCTs(BitVectorConstantType& a1, const BitVectorConstantType& a2)
 {
    CALL("BitVectorOperations::addBVCTs(BitVectorConstantType&,BitVectorConstantType&)"); 
    ASS_EQ(a1.size(),a2.size());
        
    bool carry = false;
    bool old,val;
    for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
    {
        old = a1.getValueAt(i);
        val = a1.getValueAt(i)^a2.getValueAt(i)^carry;
        a1.setValueAt(i,val);
        carry = ((old && carry && !a2.getValueAt(i)) || (a2.getValueAt(i) && carry && !old) || (a2.getValueAt(i) && !carry && old) ||(a2.getValueAt(i) && carry && old));
    }
    return carry;
 }

 // TODO: possibly change unsigned to IntegerConstantType
 void BitVectorOperations::inplaceShiftLeft(BitVectorConstantType& in, unsigned shiftByNum)
 {
    CALL("BitVectorOperations::inplaceShiftLeft(BitVectorConstantType&,unsigned)"); 
    //int startAt = in.size()-shiftByNum - 1;
    int startAt = in.size() - shiftByNum;
    
    while (startAt>0)
    {
        in.setValueAt(startAt+shiftByNum-1,in.getValueAt(startAt-1));
        --startAt;
    }
    
    for (unsigned i = 0 ; i < shiftByNum && i<in.size(); ++i){
      in.setValueAt(i,false);
    }
 }

 void BitVectorOperations::inPlaceShiftRight(BitVectorConstantType& input, unsigned shiftByNum)
 {
    CALL("BitVectorOperations::inplaceShiftRight(BitVectorConstantType&,unsigned)"); 
    unsigned startAt = shiftByNum;
    for (unsigned i = 0 ; i < input.size() - shiftByNum; ++i,++startAt){
        input.setValueAt(startAt - shiftByNum, input.getValueAt(startAt)); 
    }
    for (unsigned k = input.size()-1, i = 0 ; i<shiftByNum; --k,++i){
        input.setValueAt(k,false);
    }
  }
 
 void BitVectorOperations::inPlaceArithmeticShiftRight(BitVectorConstantType& input, unsigned shiftByNum)
 {
    CALL("BitVectorOperations::inPlaceArithmeticShiftRight(BitVectorConstantType&,unsigned)"); 
    bool sign = input.getValueAt(input.size()-1);
    unsigned startAt = shiftByNum;
    for (unsigned i = 0 ; i < input.size() - shiftByNum; ++i,++startAt){
        input.setValueAt(startAt - shiftByNum, input.getValueAt(startAt)); 
    }
    for (unsigned k = input.size()-1, i = 0 ; i<shiftByNum; --k,++i){
        input.setValueAt(k,sign);
    }
 }
   
void BitVectorOperations::multBVCTByTen(BitVectorConstantType& arg1)
{
    CALL("BitVectorOperations::multBVCTByTen(BitVectorConstantType&)"); 
    ASS(arg1.size()>0);
    
    BitVectorConstantType t(arg1.getBinArray());
    inplaceShiftLeft(arg1,1);
    inplaceShiftLeft(t,3);
    addBVCTs(arg1,t);
}  
void BitVectorOperations::specialMultBVCTByTen(BitVectorConstantType& arg1)
{
    CALL("BitVectorOperations::specialmultBVCTByTen(BitVectorConstantType&)"); 
    ASS(arg1.size()>0);
    inplaceShiftLeft(arg1,1);
} 

BitVectorConstantType BitVectorOperations::getZeroBVCT(unsigned size)
 {
    CALL("BitVectorOperations::getZeroBVCT(unsigned)"); 
    BitVectorConstantType res(size);
    for (unsigned i =0; i < size; ++i){
        res.setValueAt(i,false);
    }
        return res;
 }
void BitVectorOperations::makeZeroBVCT(BitVectorConstantType& in)
{
    CALL("BitVectorOperations::makeZeroBVCT(BitVectorConstantType&)");
    for (unsigned i =0; i < in.size() ; ++i)
        in.setValueAt(i,false);
}
  
  
BitVectorConstantType BitVectorOperations::getOneBVCT(unsigned size)
{
    CALL("BitVectorOperations::getOneBVCT(unsigned)");
    BitVectorConstantType res(size);
    res.setValueAt(0,true);
    for (unsigned i =1; i < size; ++i){
        res.setValueAt(i,false);
    }
    return res;
}

void BitVectorOperations::makeOneBVCT(BitVectorConstantType& in)
{
    CALL("BitVectorOperations::makeOneBVCT(BitVectorConstantType&)");
    in.setValueAt(0,true);
    for (unsigned i =1; i < in.size(); ++i){
        in.setValueAt(i,false);
    }
}
  

void BitVectorOperations::makeAllOnesBVCT(BitVectorConstantType& in)
{
    CALL("BitVectorOperations::makeAllOnesBVCT(BitVectorConstantType&)");
    for (unsigned i = 0 ; i < in.size(); ++ i){
        in.setValueAt(i,true);
    }
}
BitVectorConstantType BitVectorOperations::getAllOnesBVCT(unsigned size)
{
    CALL("BitVectorOperations::getAllOnesBVCT(unsigned)");
    DArray<bool> allOne(size);
        
    for (unsigned i = 0 ; i < size; ++ i){
        allOne[i] = true;
    }
    BitVectorConstantType res(size);
    res.setBinArray(allOne);
    return res;
}
  
void BitVectorOperations::bvnand(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvnand(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
    DArray<bool> a1 = arg1.getBinArray();
    DArray<bool> a2 = arg2.getBinArray();
        
    for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
        result.setValueAt(i,!(a1[i] && a2[i]));
}
   
void BitVectorOperations::subtractBVCTs(BitVectorConstantType& a1, const BitVectorConstantType& a2)
{
    CALL("BitVectorOperations::subtractBVCTs(BitVectorConstantType&, const BitVectorConstantType&)");
    ASS_EQ(a1.size(),a2.size());
        
    BitVectorConstantType arg2Notted(a1.size());
    bvnot(a2,arg2Notted);
    addBVCTs(a1,arg2Notted);
    BitVectorConstantType one = getOneBVCT(a1.size());
    addBVCTs(a1,one);
}
   
void BitVectorOperations::bvneg(const BitVectorConstantType& arg, BitVectorConstantType& res)
{
    CALL("BitVectorOperations::bvneg(const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg.size(),res.size());
    bool encounteredOne = false;
    for (unsigned i = 0; i<arg.size(); ++i){
        if (encounteredOne){
            res.setValueAt(i,!arg.getValueAt(i));
        }
        else{
            if (arg.getValueAt(i) == true)
                encounteredOne = true;
            res.setValueAt(i, arg.getValueAt(i));
        }
    }
}
   
void BitVectorOperations::bvnot(const BitVectorConstantType& arg, BitVectorConstantType& res)
{
    CALL("BitVectorOperations::bvnot(const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg.size(),res.size());
    for (unsigned i = 0; i<arg.size();++i){
        res.setValueAt(i, !arg.getValueAt(i));
    }
}
   
bool BitVectorOperations::bvadd(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvadd(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
    DArray<bool> a1 = arg1.getBinArray();
    DArray<bool> a2 = arg2.getBinArray();
        
    bool carry = false;
    for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
    {
        result.setValueAt(i,a1[i] ^ a2[i] ^ carry);
        carry = ((a1[i] && carry && !a2[i]) || (a2[i] && carry && !a1[i]) || (a2[i] && !carry && a1[i]) ||(a2[i] && carry && a1[i]));
    }
    return carry;
}
   
void BitVectorOperations::bvor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvor(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
    DArray<bool> a1 = arg1.getBinArray();
    DArray<bool> a2 = arg2.getBinArray();
        
    for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
        result.setValueAt(i,a1[i] || a2[i]);
}
   
void BitVectorOperations::bvxor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvxor(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
    DArray<bool> a1 = arg1.getBinArray();
    DArray<bool> a2 = arg2.getBinArray();
        
    for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
        result.setValueAt(i,a1[i] ^ a2[i]);
}
   
void BitVectorOperations::bvnor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvnor(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
    DArray<bool> a1 = arg1.getBinArray();
    DArray<bool> a2 = arg2.getBinArray();
        
    for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
        result.setValueAt(i,!(a1[i] || a2[i]));
}

void BitVectorOperations::bvxnor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvxnor(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
    DArray<bool> a1 = arg1.getBinArray();
    DArray<bool> a2 = arg2.getBinArray();
        
    for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
        result.setValueAt(i,(a1[i] == a2[i]));
}

void BitVectorOperations::bvmul(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvmul(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
    ASS(isZero(result));

    BitVectorConstantType toAdd(arg2.getBinArray());
    unsigned lastI = 0;
    unsigned diff;
    for (unsigned i = 0 ; i < arg1.size() ; ++ i)
    {
        if (arg1.getValueAt(i))
        {
            diff = i - lastI;
            inplaceShiftLeft(toAdd,diff);
            addBVCTs(result,toAdd);
            lastI = i;
        }
    }
}
   
void BitVectorOperations::bvurem(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvurem(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
        
    //  bvurem returns its first operand if the second operand is 0
    result = arg1;
    if (isZero(arg2))
    {
        return;
    }
       
    bool done = false;
    bvult(result,arg2,done);
    
    while (!done)
    {
        subtractBVCTs(result,arg2);
        bvult(result,arg2,done);
    }
}

//TODO: simplify?
void BitVectorOperations::bvudiv_fast(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvudiv_fast(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
        
    unsigned indexLastOneArg2;
    bool containsOne = getIndexOfLastOne(arg2,indexLastOneArg2);
    
    if (!containsOne)
    {
        makeAllOnesBVCT(result);
        return;
    }
    
    BitVectorConstantType buffer(arg1.size());
    unsigned j = buffer.size()-1;
    for (unsigned k = 0; k < indexLastOneArg2;++k,--j)
        result.setValueAt(j,false);
   
    specialExtract(arg1,indexLastOneArg2,buffer);
    unsigned indexWorkingAtArg1 = arg1.size() - indexLastOneArg2 - 1;
    bool fitIn= false;
    
    while(indexWorkingAtArg1!=0)
    {
        bvuge(buffer,arg2,fitIn);
        if (fitIn)
            subtractBVCTs(buffer,arg2);
        
        result.setValueAt(j,fitIn);
        //shift left in order to take into account next bit
        inplaceShiftLeft(buffer,1);
        --indexWorkingAtArg1;
        buffer.setValueAt(0,arg1.getValueAt(indexWorkingAtArg1));
        --j;
    }
    bvuge(buffer,arg2,fitIn);
    result.setValueAt(j,fitIn);
}


void BitVectorOperations::specialExtract(const BitVectorConstantType& arg1, unsigned indexLastOneArg2, BitVectorConstantType& result)
{
    ASS_EQ(arg1.size(),result.size());
    unsigned j = arg1.size()-indexLastOneArg2-1;
    unsigned i = 0;
    for (; i <= indexLastOneArg2; ++i,++j){
        result.setValueAt(i,arg1.getValueAt(j));
    }
    for (;i<arg1.size();++i){
        result.setValueAt(i,false);
    }
}  

//TODO: simplify?
void BitVectorOperations::bvurem_fast(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvurem_fast(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
        
    unsigned indexLastOneArg2;
    bool containsOne = getIndexOfLastOne(arg2,indexLastOneArg2);
    
    if (!containsOne)
    {
        result = arg1;
        return;
    }
    
    specialExtract(arg1,indexLastOneArg2,result);
    unsigned indexWorkingAtArg1 = arg1.size() - indexLastOneArg2 - 1;
    bool fitIn= false;
    
    while(indexWorkingAtArg1!=0)
    {
        
        bvuge(result,arg2,fitIn);
        if (fitIn)
            subtractBVCTs(result,arg2);
            
        inplaceShiftLeft(result,1);
        --indexWorkingAtArg1;
        result.setValueAt(0,arg1.getValueAt(indexWorkingAtArg1));
        
    }
    bvuge(result,arg2,fitIn);
    if (fitIn){
        subtractBVCTs(result,arg2);
    }
    
}
void BitVectorOperations::printBVCT(const BitVectorConstantType& arg1)
{
    int j = arg1.size()-1;
    cout<<endl<<"print BVCT:"<<endl;
    for (;j>=0;--j)
    {
        cout<<arg1.getValueAt(j);
    }
    cout<<endl<<"end"<<endl;
}
void BitVectorOperations::bvudiv(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvudiv(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
        
    //  bvudiv now returns a vector of all 1's if the second operand is 0
    if (isZero(arg2))
    {
        makeAllOnesBVCT(result);
        return;
    }
    
    BitVectorConstantType one(arg1.size());
    makeOneBVCT(one);
    BitVectorConstantType workWith;
    workWith = arg1;
    bool done = false;
    bvult(workWith,arg2,done);
    
    while (!done)
    {
        subtractBVCTs(workWith,arg2);
        addBVCTs(result,one);
        bvult(workWith,arg2,done);
    }
}
   
void BitVectorOperations::bvsdiv(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvsdiv(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
        
    bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
    bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
    if (!msb_arg1 && !msb_arg2)
    {
        bvudiv_fast(arg1,arg2,result);
        return;
    }
    if (msb_arg1 && !msb_arg2)
    {
        BitVectorConstantType arg1Negated(arg1.size());
        bvneg(arg1,arg1Negated);
            
        BitVectorConstantType div(arg1.size());
        bvudiv_fast(arg1Negated,arg2,div);
        bvneg(div,result);
        return;
    }
    if (!msb_arg1 && msb_arg2)
    {
        BitVectorConstantType arg2Negated(arg2.size());
        BitVectorConstantType div(arg1.size());
        bvudiv_fast(arg1,arg2Negated,div);
        bvneg(div,result);
        return;
    }
    // negate both and do a bvudiv
    BitVectorConstantType arg1Negated(arg1.size());
    BitVectorConstantType arg2Negated(arg2.size());
    bvneg(arg1,arg1Negated);
    bvneg(arg2,arg2Negated);
    bvudiv_fast(arg1Negated,arg2Negated,result);
}
   
void BitVectorOperations::bvsrem(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
{
    CALL("BitVectorOperations::bvsrem(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
    ASS_EQ(arg1.size(),arg2.size());
    ASS_EQ(arg2.size(),result.size());
        
    bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
    bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
        
    if (!msb_arg1 && !msb_arg2)
    {
        bvurem_fast(arg1,arg2,result);
        return;
    }
        
    if (msb_arg1 && !msb_arg2)
    {
        BitVectorConstantType arg1Negated(arg1.size());
        bvneg(arg1,arg1Negated);
        BitVectorConstantType rem(arg1.size());
        bvurem_fast(arg1Negated,arg2,rem);
        bvneg(rem,result);
        return;
    }
        
    if (!msb_arg1 && msb_arg2)
    {
        BitVectorConstantType arg2Negated(arg1.size());
        bvneg(arg2,arg2Negated);
        bvurem_fast(arg1,arg2Negated,result);
        return;
    }
        
    BitVectorConstantType arg1Negated(arg1.size());
    BitVectorConstantType arg2Negated(arg2.size());
    bvneg(arg1,arg1Negated);
    bvneg(arg2,arg2Negated);
        
    BitVectorConstantType rem(arg2.size());
    bvurem_fast(arg1Negated,arg2Negated,rem);
        
    bvneg(rem,result);
}
   
   void BitVectorOperations::bvsmod(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::bvsmod(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
        bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
        
        BitVectorConstantType arg1Abs(arg1);
        BitVectorConstantType arg2Abs(arg2);
        
        if(msb_arg1)
        {
            BitVectorConstantType arg1Negated(arg1.size());
            bvneg(arg1,arg1Negated);
            arg1Abs = arg1Negated;
        }
        if(msb_arg2)
        {
            BitVectorConstantType arg2Negated(arg2.size());
            bvneg(arg2,arg2Negated);
            arg2Abs = arg2Negated;
        }
        
        BitVectorConstantType u(arg1.size());
        bvurem_fast(arg1Abs,arg2Abs,u);
        
        if (isZero(u))
        {
            result = u;
            return;
        }
        if (!msb_arg1 && !msb_arg2)
        {
            result = u;
            return;
        }
        
        if (msb_arg1 && !msb_arg2)
        {
            BitVectorConstantType uNegated(arg1.size());
            bvneg(u,uNegated);
            bvadd(uNegated,arg2,result);
            return;
        }
        
        if (!msb_arg1 && msb_arg2)
        {
            bvadd(u,arg2,result);
            return;
        }
        
        bvneg(u,result);
        
    }
   void BitVectorOperations::bvand(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::bvand(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
         
        for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,a1[i] && a2[i]);
          
   }  
   
   void BitVectorOperations::bvshl(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::bvshl(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        // use log base 2 eg logbase2 size of bitvector
        result = arg1;
        double sum = 0,numL;
        unsigned terminateIndex = (unsigned)(ceil(log2(arg2.size())));
        for (unsigned i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i))
            {
                numL = pow(2,i); // 
                sum+=numL;
                if(numL>=arg1.size() || sum>=arg1.size() || i>=terminateIndex)
                {    
                    makeZeroBVCT(result);
                    break;
                }
                unsigned num = static_cast<unsigned>(numL);
                inplaceShiftLeft(result,num);
            }
        }
    }
   
   void BitVectorOperations::bvlshr(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::bvlshr(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        result = arg1;
        double sum = 0, numL;
        unsigned terminateIndex = (unsigned)(ceil(log2(arg2.size())));
        for (unsigned i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i))
            {
                numL = pow(2,i); 
                sum+=numL;
                if (numL>=arg1.size() || sum>=arg1.size() || i>=terminateIndex)
                {
                    makeZeroBVCT(result);
                    break;
                }
                unsigned num = static_cast<unsigned>(numL);
                inPlaceShiftRight(result,num);
             }
        }
    }
   
   void BitVectorOperations::bvashr(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::bvashr(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        result = arg1;
        double sum = 0,numL;
        unsigned terminateIndex = (unsigned)(ceil(log2(arg2.size())));
        for (unsigned i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i))
            {
                numL = pow(2,i); 
                sum+=numL;
                if (numL>=arg1.size() || sum>=arg1.size() || i>=terminateIndex)
                {
                    makeZeroBVCT(result);
                    break;
                }
                unsigned num = static_cast<unsigned>(numL);
                inPlaceArithmeticShiftRight(result,num);
            }
        }
    }
   
   void BitVectorOperations::bvsub(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::bvsub(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        BitVectorConstantType arg2Notted(arg1.size());
        bvnot(arg2,arg2Notted);
        BitVectorConstantType res(arg1.size());
        bvadd(arg1,arg2Notted,res);
        BitVectorConstantType one = getOneBVCT(arg1.size());
        bvadd(res,one,result);
        
    }
   
   void BitVectorOperations::bvcomp(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::bvcomp(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(1,result.size());
        bool areEqual = true;
        for (unsigned i = 0 ; i < arg1.size(); ++i){
            if (arg1.getValueAt(i) != arg2.getValueAt(i))
            {
                areEqual = false;
                break;
            }
        }
        result.setValueAt(0,areEqual);
    }
   
   void BitVectorOperations::zero_extend(unsigned extendBy, const BitVectorConstantType& arg , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::zero_extend(unsigned, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(result.size(),arg.size()+extendBy);
        unsigned i = 0;
        for (; i < arg.size();++i){
            result.setValueAt(i,arg.getValueAt(i));
        }
        
        //unnecessary loop?
        for (unsigned j = 0 ; j < extendBy;++i,++j){
            result.setValueAt(i,false);
        }
    }
   
   void BitVectorOperations::repeat(unsigned multBy, const BitVectorConstantType& arg , BitVectorConstantType& result)
    {
       CALL("BitVectorOperations::repeat(unsigned, const BitVectorConstantType&, BitVectorConstantType&)");
       ASS_EQ(result.size(),arg.size()*multBy);
       
       unsigned j = 0;
       while (j<result.size()){
           for (unsigned i = 0 ; i < arg.size(); ++i,++j ){
               result.setValueAt(j,arg.getValueAt(i));
           }
       }
    }
   
   void BitVectorOperations::sign_extend(unsigned extendBy, const BitVectorConstantType& arg , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::sign_extend(unsigned, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(result.size(),arg.size()+extendBy);
        bool sign = result.getValueAt(result.size()-1);
        unsigned i = 0;
        for (; i < arg.size();++i){
            result.setValueAt(i,arg.getValueAt(i));
        }
        for (unsigned j = 0 ; j < extendBy;++i,++j){
            result.setValueAt(i,sign);
        }
    }
   
   void BitVectorOperations::rotate_right(IntegerConstantType in, const BitVectorConstantType& arg , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::rotate_right(IntegerConstantType, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg.size(),result.size());
        
        unsigned rotateBy = in.toInner();
        unsigned newRotateBy = rotateBy;
        if (rotateBy > arg.size())
            newRotateBy = rotateBy-arg.size();
        for (unsigned i = 0 ; i < arg.size();++i){
            bool theValue = arg.getValueAt(i);
            unsigned newIndex;
            if (i < newRotateBy){
                newIndex = arg.size() - newRotateBy + i ;
            }
            else{
                newIndex = i - newRotateBy;
            }
            
            result.setValueAt(newIndex,theValue);
        }
    }
   
   void BitVectorOperations::rotate_left(IntegerConstantType in, const BitVectorConstantType& arg , BitVectorConstantType& result)
    {
       ASS_EQ(arg.size(),result.size());
        
        unsigned rotateBy = in.toInner();
        unsigned newRotateBy = rotateBy;
        if (rotateBy > arg.size())
            newRotateBy = rotateBy-arg.size();
        for (unsigned i = 0 ; i < arg.size();++i){
            bool theValue = arg.getValueAt(i);
            unsigned newIndex;
            if (newRotateBy+i >= arg.size()){
               
                unsigned diff = arg.size() - i;
                 newIndex = newRotateBy - diff;
            }
            else{
                newIndex = i + newRotateBy;
            }
            
            result.setValueAt(newIndex,theValue);
        }
    }
   
   void BitVectorOperations::concat(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        CALL("BitVectorOperations::concat(const BitVectorConstantType&, const BitVectorConstantType&, BitVectorConstantType&)");
        ASS_EQ(arg1.size()+arg2.size(),result.size());
        unsigned i;
        for (i = 0 ; i<arg2.size(); ++i ){
            result.setValueAt(i,arg2.getValueAt(i));
        }
        for (unsigned j = 0; j < arg1.size(); ++j , ++i){
            result.setValueAt(i,arg1.getValueAt(j));
        }
    }
   
   void BitVectorOperations::extract(unsigned upper, unsigned lower, const BitVectorConstantType& in, BitVectorConstantType& result)
    {
        ASS_EQ(upper-lower+1,result.size());
        DArray<bool> resultArray(upper-lower+1);
        for (unsigned i = 0 ; i < result.size(); ++i){
            resultArray[i] = in.getValueAt(lower);
            ++lower;
        }
        result.setBinArray(resultArray);
    }
   
   void BitVectorOperations::bvule(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        CALL("BitVectorOperations::bvule(const BitVectorConstantType&, const BitVectorConstantType&, bool&)");
        ASS_EQ(arg1.size(),arg2.size());
        
        unsigned size = arg1.size();
       
        if (arg1 == arg2)
            result = true;
        else
        {
            BitVectorConstantType arg2Notted(size);
            bvnot(arg2,arg2Notted);
            const BitVectorConstantType one = getOneBVCT(size);
            bool carry = addBVCTs(arg2Notted,arg1);
            result = !(addBVCTs(arg2Notted,one) || carry);
        }     
    }
   
   void BitVectorOperations::bvuge(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        CALL("BitVectorOperations::bvuge(const BitVectorConstantType&, const BitVectorConstantType&, bool&)");
        ASS_EQ(arg1.size(),arg2.size());
        
        unsigned size = arg1.size();
        BitVectorConstantType arg2Notted(size);
              
        BitVectorOperations::bvnot(arg2,arg2Notted);
        bool carry = addBVCTs(arg2Notted, arg1);
              
        BitVectorConstantType one = getOneBVCT(size);
        result = addBVCTs(arg2Notted,one) || carry;
              
    }
   
  void BitVectorOperations::bvugt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        CALL("BitVectorOperations::bvugt(const BitVectorConstantType&, const BitVectorConstantType&, bool&)");
        ASS_EQ(arg1.size(),arg2.size());
        
        unsigned size = arg1.size();
        BitVectorConstantType arg2Notted(size);
        bvnot(arg2,arg2Notted);
        BitVectorConstantType one = getOneBVCT(size);
        
        bool carry = addBVCTs(arg2Notted, arg1);
        bool tempResult = addBVCTs(arg2Notted,one) || carry;
        
        if ((carry && isZero(arg2Notted)) || (tempResult && isZero(arg2Notted)))
            result = false;
        else
            result = tempResult;
    }
   
   void BitVectorOperations::bvult(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        CALL("BitVectorOperations::bvulte(const BitVectorConstantType&, const BitVectorConstantType&, bool&)");
        ASS_EQ(arg1.size(),arg2.size());
        bvugt(arg2,arg1,result);
    }
   
   void BitVectorOperations::bvslt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        CALL("BitVectorOperations::bvslt(const BitVectorConstantType&, const BitVectorConstantType&, bool&)");
        ASS_EQ(arg1.size(),arg2.size());
        result = false;
        bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
        bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
        
        if (msb_arg1 && !msb_arg2)
        {
            result = true;
            return;
        }
        if (msb_arg1 == msb_arg2)
        {
            bvult(arg1,arg2,result);
        }
        
    }
   
   void BitVectorOperations::bvsle(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        CALL("BitVectorOperations::bvsle(const BitVectorConstantType&, const BitVectorConstantType&, bool&)");
        ASS_EQ(arg1.size(),arg2.size());
        result = false;
        bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
        bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
        
        if (msb_arg1 && !msb_arg2)
        {
            result= true;
            return;
        }
        if (msb_arg1 == msb_arg2)
        {
            bvule(arg1,arg2,result);
        }
    }
   
   void BitVectorOperations::bvsgt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        CALL("BitVectorOperations::bvsgt(const BitVectorConstantType&, const BitVectorConstantType&, bool&)");
        ASS_EQ(arg1.size(),arg2.size());
        bvslt(arg2,arg1,result);
    }
   
   void BitVectorOperations::bvsge(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        CALL("BitVectorOperations::bvsge(const BitVectorConstantType&, const BitVectorConstantType&, bool&)");
        ASS_EQ(arg1.size(),arg2.size());
        bvsle(arg2,arg1,result);
    }

}
