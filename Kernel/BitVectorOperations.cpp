
#include "BitVectorOperations.hpp"


namespace Kernel{




//static bool map[][bool] = {zero, one,fifteen};
static DHMap<char, BitVectorConstantType> map;


void BitVectorOperations::createHashmap()
{
    static bool zero[] = {false}; // 0 
    static bool one[] = {true}; // 1
    static bool two[] = {false, true}; // 01
    static bool three[] = {true, true}; // 11
    static bool four[] = {false, false, true}; // 001
    static bool five[] = {true, false, true}; // 101
    static bool six[] = {false, true, true}; // 011
    static bool seven[] = {true, true, true}; // 111
    static bool eight[] = {false, false, false, true}; // 0001
    static bool nine[] = {true, false, false, true}; // 1001
    static bool ten[] = {false, true, false, true}; // 0101
    static bool eleven[] = {true, true, false, true}; // 1101
    static bool twelve[] = {false, false, true, true}; // 0011
    static bool thirteen[] = {true, false, true, true}; // 1011
    static bool fourteen[] = {false, true, true, true}; // 0111
    static bool fifteen[] = {true, true, true, true}; // 1111

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

/*BitVectorConstantType BitVectorOperations::getBVCTFromVString(vstring& numberToRepresent, unsigned size)
{
    char initialChar = numberToRepresent[0];
    
    BitVectorConstantType initial = getBVCTFromDec(initialChar);
    BitVectorConstantType step = fitBVCTIntoBits(initial, size);
    BitVectorConstantType initialBoolArray(step);
    
    BitVectorConstantType smallestBinArrayTen = getBVCTFromDec('a');
    //printBoolArrayContent(smallestBinArrayTen.getBinArray());
    BitVectorConstantType binArrayTen = fitBVCTIntoBits(smallestBinArrayTen, size);
   // printBoolArrayContent(binArrayTen.getBinArray());
    
    for(unsigned int i = 1; i<numberToRepresent.length(); i++) {
        char c = numberToRepresent[i]; 
        BitVectorConstantType multipliedByTen = multBVCTs(initialBoolArray, binArrayTen); 
        BitVectorConstantType toAdd = getBVCTFromDec(c);
        BitVectorConstantType toAddPadded = fitBVCTIntoBits(toAdd,size);
        DArray<bool> added(size);
        addBinArrays(multipliedByTen.getBinArray(),toAddPadded.getBinArray(), added);
        initialBoolArray.setBinArray(added);
        //printBoolArrayContent(initialBoolArray.getBinArray());
    }
    //cout<<"result of multiplication is "<<endl;
    //printBoolArrayContent(initialBoolArray.getBinArray());
    return initialBoolArray;
}*/
 
BitVectorConstantType BitVectorOperations::getBVCTFromVString(vstring& numberToRepresent, unsigned size)
{
    
    char initialChar = numberToRepresent[0];
    
    BitVectorConstantType initialBoolArray = getBVCTFromDec(initialChar,size);
    BitVectorConstantType binArrayTen = getBVCTFromDec('a',size);
    BitVectorConstantType sum(initialBoolArray.getBinArray());
    char c;
    BitVectorConstantType toAddPadded; 
    
    for(unsigned int i = 1; i<numberToRepresent.length(); i++) {
        multBVCTs(sum,binArrayTen,sum);
        c = numberToRepresent[i]; 
        toAddPadded = getBVCTFromDec(c,size);
        addBVCTs(sum,toAddPadded,sum);
        
    }
    //cout<<"getBVCTFromVString:"<<endl;
    //printBoolArrayContent(sum.getBinArray());
    return sum;
} 

BitVectorConstantType BitVectorOperations::fitBVCTIntoBits(BitVectorConstantType input, unsigned size)
{
    
    if (input.size()==size)
        return input;
    else if (input.size()<size)
    {
        BitVectorConstantType result = padBVCT(input, size);
        return result;
    }
    else 
    {
        BitVectorConstantType result = truncate(input, size);
        return result;
    }
}


BitVectorConstantType BitVectorOperations::padBVCT(BitVectorConstantType input, unsigned size)
{
    if (input.size() == size)
        return input;
   
    DArray<bool> result(size);
    DArray<bool> anArray = input.getBinArray();
    
    unsigned i;
    for (i = 0 ; i< anArray.size(); ++i){
        result[i] = anArray[i];
    }
    for (;i<size;++i){
        result[i] = false;
    }
    BitVectorConstantType r(result);
    return r;
}

BitVectorConstantType BitVectorOperations::truncate(BitVectorConstantType in, unsigned size)
{
    if (in.size()==size)
        return in;
    
    DArray<bool> result(size);
    DArray<bool> input = in.getBinArray();
    for (int i = 0 , j = input.size()-1, counter = size-1; i < size; ++i, --j, -- counter)
    {
        result[i] = input[i];
    }
    BitVectorConstantType r(result);
    return r;
}

/*BitVectorConstantType BitVectorOperations::getBVCTFromDec(char n)
{
    
    switch(n){
        
        case '0':{
            DArray<bool> zeroArr;
            bool tem[] = {false, false, false,false}; // 0000 -> 0000
            zeroArr.initFromArray(4, tem);
            BitVectorConstantType res(zeroArr);
            return res;
        }
        case '1':{
            DArray<bool> oneArr;
            bool tem[] = {true, false, false,false}; // 0001 -> 1000
            oneArr.initFromArray(4, tem);
            BitVectorConstantType res(oneArr);
            return res;
        }
        case '2':{
            DArray<bool> twoArr;
            bool tem[] = {false, true, false,false}; // 0010 -> 0100
            twoArr.initFromArray(4, tem);
            BitVectorConstantType res(twoArr);
            return res;
        }
        case '3':{
            DArray<bool> threeArr;
            bool tem[] = {true, true, false, false, }; // 0011 -> 1100
            threeArr.initFromArray(4, tem);
            BitVectorConstantType res(threeArr);
            return res;
        }
        case '4':{
            DArray<bool> fourArr;
            bool tem[] = {false, false, true, false}; // 0100 -> 0010
            fourArr.initFromArray(4, tem);
            BitVectorConstantType res(fourArr);
            return res;
        }
        case '5':{
            DArray<bool> fiveArr;
            bool tem[] = {true, false, true, false}; // 0101 -> 1010
            fiveArr.initFromArray(4, tem);
            BitVectorConstantType res(fiveArr);
            return res;
        }
        case '6':{
            DArray<bool> sixArr;
            bool tem[] = {false, true, true, false}; // 0110 -> 0110
            sixArr.initFromArray(4, tem);
            BitVectorConstantType res(sixArr);
            return res;
        }
        case '7':{
            DArray<bool> sevenArr;
            bool tem[] = {true, true, true, false}; // 0111 -> 1110
            sevenArr.initFromArray(4, tem);
            BitVectorConstantType res(sevenArr);
            return res;
        }
        case '8':{
            DArray<bool> eightArr;
            bool tem[] = {false, false, false, true}; // 1000 -> 0001
            eightArr.initFromArray(4, tem);
            BitVectorConstantType res(eightArr);
            return res;
        }
        case '9':{
            DArray<bool> nineArr;
            bool tem[] = {true, false, false,true}; // 1001 -> 1001
            nineArr.initFromArray(4, tem);
            BitVectorConstantType res(nineArr);
            return res;
        }
        case 'a':
        case 'A':{
            DArray<bool> tenArr;
            bool tem[] = {false, true, false,true}; // 1010 -> 0101
            tenArr.initFromArray(4, tem);
            BitVectorConstantType res(tenArr);
            return res;
        }
        case 'b':
        case 'B':{
            DArray<bool> elevenArr;
            bool tem[] = {true, true, false, true}; // 1011 -> 1101
            elevenArr.initFromArray(4, tem);
            BitVectorConstantType res(elevenArr);
            return res;
        }
        case 'c':
        case 'C':{
            DArray<bool> twelveArr;
            bool tem[] = {false, false, true , true}; // 1100 -> 0011
            twelveArr.initFromArray(4, tem);
            BitVectorConstantType res(twelveArr);
            return res;
        }
        case 'd':
        case 'D':{
            DArray<bool> thirteenArr;
            bool tem[] = {true, false, true,true}; // 1101 -> 1011
            thirteenArr.initFromArray(4, tem);
            BitVectorConstantType res(thirteenArr);
            return res;
        }   
        case 'e':
        case 'E':{
            DArray<bool> fourteenArr;
            bool tem[] = {false, true, true, true}; // 1110 -> 0111
            fourteenArr.initFromArray(4, tem);
            BitVectorConstantType res(fourteenArr);
            return res;
        }
        case 'f':
        case 'F':{
            DArray<bool> fifteenArr;
            bool tem[] = {true, true, true,true}; // 1111 -> 1111
            fifteenArr.initFromArray(4, tem);
            BitVectorConstantType res(fifteenArr);
            return res;
        }
        default:
            throw Exception("between 0 and 15");
        
    }

}*/

// this function is now assuming a1 and result are/can be the same 
// a1 and a2 have to be same length, result also has to be of same length  
bool BitVectorOperations::addBVCTs(BitVectorConstantType& a1, BitVectorConstantType& a2, BitVectorConstantType& result)
{
    ASS_EQ(a1.size(),a2.size());
    ASS_EQ(a2.size(),result.size());
   
    bool carry = false;
    for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
    {
        bool old = a1.getValueAt(i);
        bool val = a1.getValueAt(i)^a2.getValueAt(i)^carry;
        //cout<<"i: "<<i<<" a1[i]: "<<a1.getValueAt(i)<<" a2[i]: "<<a2.getValueAt(i)<<" and val is "<<val<<endl;
        result.setValueAt(i,val);
        carry = ((old && carry && !a2.getValueAt(i)) || (a2.getValueAt(i) && carry && !old) || (a2.getValueAt(i) && !carry && old) ||(a2.getValueAt(i) && carry && old));
    }
    
    return carry;
}
/*bool BitVectorOperations::addBinArrays(const DArray<bool>& a1, const DArray<bool>& a2, DArray<bool> &result)
{
    ASS_EQ(a1.size(),a2.size());
    ASS_EQ(a2.size(),result.size());
   
    bool carry = false;
    for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
    {
        result[i] = a1[i] ^ a2[i] ^ carry;
        if ((a1[i] && carry && !a2[i]) || (a2[i] && carry && !a1[i]) || (a2[i] && !carry && a1[i]) ||(a2[i] && carry && a1[i]))
            carry = true;
        else
            carry = false;
        carry = ((a1[i] && carry && !a2[i]) || (a2[i] && carry && !a1[i]) || (a2[i] && !carry && a1[i]) ||(a2[i] && carry && a1[i]));

    }
    
    return carry;
}*/
void BitVectorOperations::multBVCTs(BitVectorConstantType& in1, BitVectorConstantType& in2, BitVectorConstantType& res)
{
    ASS_EQ(in1.size(),in2.size());
    ASS_EQ(in2.size(),res.size());

    DArray<bool> a1 = in1.getBinArray();
    DArray<bool> a2 = in2.getBinArray();
    BitVectorConstantType sum(in1.size());
    
    DArray<bool> curr;
    BitVectorConstantType toAdd;
    for (int i = 0, j = a1.size()-1 ; i < a1.size() ; ++ i,--j )
    {
        if (a1[i] == true)
        {
            toAdd= shiftLeft(a2,i);
            addBVCTs(sum,toAdd,sum);
        }
    }
    
    res.setBinArray(sum.getBinArray());
}   


BitVectorConstantType BitVectorOperations::shiftLeft(DArray<bool>& input, unsigned shiftByNum)
{
    DArray<bool> res(input.size());
    BitVectorConstantType result;
    unsigned k;
    for (k = 0 ; k < shiftByNum ; ++k){
        res[k] = false;
    }
    
    for (unsigned i = 0 ; k< input.size(); ++k, ++i){
        res[k] = input[i];
    }
    result.setBinArray(res);
    return result;
}

void BitVectorOperations::printBoolArrayContent(DArray<bool> array)
{
    for (int i = array.size()-1 ; i > -1 ; --i)
    {
        if (array[i] == false)
            cout<<"0";
        else if (array[i] == true)
            cout<<"1";
        
    }
    cout<< endl;
}

}