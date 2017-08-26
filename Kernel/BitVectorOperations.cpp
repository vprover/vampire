
#include "BitVectorOperations.hpp"


namespace Kernel{




//static bool map[][bool] = {zero, one,fifteen};
static DHMap<char, BitVectorConstantType> map;


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
    
    // 11 = 'b'
    toAdd.initFromArray(4,eleven);
    bvToAdd.setBinArray(toAdd);
    map.insert('b',bvToAdd);
    
    // 12 = 'c'
    toAdd.initFromArray(4,twelve);
    bvToAdd.setBinArray(toAdd);
    map.insert('c',bvToAdd);
    
    // 13 = 'd'
    toAdd.initFromArray(4,thirteen);
    bvToAdd.setBinArray(toAdd);
    map.insert('d',bvToAdd);
    
    // 14 = 'e'
    toAdd.initFromArray(4,fourteen);
    bvToAdd.setBinArray(toAdd);
    map.insert('e',bvToAdd);
    
    // 15 = 'f'
    toAdd.initFromArray(4,fifteen);
    bvToAdd.setBinArray(toAdd);
    map.insert('f',bvToAdd);
    
}



BitVectorConstantType BitVectorOperations::getBVCTFromDec(char n, unsigned size)
{
    
    BitVectorConstantType bvct = map.get(n);
    BitVectorConstantType res(size);
    unsigned i = 0 ;
    
    for (; i < size && i<bvct.size(); ++ i){
        res.setValueAt(i,bvct.getValueAt(i));
    
    }
    for ( ; i < size; ++ i){
        res.setValueAt(i,false);
    
    }
    return res;
}
    
vstring BitVectorOperations::boolArraytoString(const DArray<bool>& in){
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

DArray<char> BitVectorOperations::getHexArrayFromString(vstring& input)
{
    ASS(input.length()>0);

    DArray<char> result(input.length());
    for (unsigned i = input.length()-1, j = 0; j<input.length(); --i,++j){
        if ((input.at(i) >= '0' && input.at(i) <= '9') || (input.at(i) >= 'a' && input.at(i) <= 'f') || (input.at(i) >= 'A' && input.at(i) <= 'F'))
            result[j] = input[j];
        else
            ASS(1==2);
    }
    return result;
} 
// get a BVCT from a string like this 010010
BitVectorConstantType BitVectorOperations::getBoolArrayFromVString(vstring& input)
 {
    BitVectorConstantType result(input.length());
    for (int j = 0, i = input.length()-1; i>=0;--i, ++j){
        if (input.at(j) == '0')
            result.setValueAt(i,false);
        else if (input.at(j) == '1')
            result.setValueAt(i,true);
        else
            ASS(2==3);
        
    }
    return result;

  }
BitVectorConstantType BitVectorOperations::getBVCTFromVString(vstring& numberToRepresent, unsigned size)
{
    
    char initialChar = numberToRepresent[0];
    
    BitVectorConstantType initialBoolArray = getBVCTFromDec(initialChar,size);
    BitVectorConstantType sum(initialBoolArray.getBinArray());
    char c;
    BitVectorConstantType toAddPadded; 
    
    for(unsigned i = 1; i<numberToRepresent.length(); i++) {
        multBVCTByTen(sum);
        c = numberToRepresent[i]; 
        toAddPadded = getBVCTFromDec(c,size);
        addBVCTs(sum,toAddPadded);
        
    }
    return sum;
} 
 bool BitVectorOperations::addBVCTs(BitVectorConstantType& a1, const BitVectorConstantType& a2)
    {
        ASS_EQ(a1.size(),a2.size());
        
        bool carry = false;
        for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
        {
            bool old = a1.getValueAt(i);
            bool val = a1.getValueAt(i)^a2.getValueAt(i)^carry;
            a1.setValueAt(i,val);
            carry = ((old && carry && !a2.getValueAt(i)) || (a2.getValueAt(i) && carry && !old) || (a2.getValueAt(i) && !carry && old) ||(a2.getValueAt(i) && carry && old));
        }

        return carry;
    }

 void BitVectorOperations::inplaceShiftLeft(BitVectorConstantType& in, unsigned shiftByNum)
    {
        //int startAt = in.size()-shiftByNum - 1;
        unsigned startAt = in.size() - shiftByNum;
        
        while (startAt>0)
        {
            in.setValueAt(startAt+shiftByNum-1,in.getValueAt(startAt-1));
            --startAt;
        }
        for (unsigned i = 0 ; i < shiftByNum; ++i){
            in.setValueAt(i,false);
        }
    }
   

void BitVectorOperations::multBVCTByTen(BitVectorConstantType& arg1)
{
    ASS(arg1.size()>0);
    
    BitVectorConstantType t(arg1.getBinArray());
    inplaceShiftLeft(arg1,1);
    inplaceShiftLeft(t,3);
    addBVCTs(arg1,t);
}  
void BitVectorOperations::printBoolArrayContent(DArray<bool> array)
{
    for (unsigned i = array.size()-1 ; i > -1 ; --i)
    {
        if (array[i] == false)
            cout<<"0";
        else if (array[i] == true)
            cout<<"1";
        
    }
    cout<< endl;
}

}