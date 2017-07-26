
#include "BitVectorOperations.hpp"


namespace Kernel{



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

BitVectorConstantType BitVectorOperations::getBVCTFromVString(vstring& numberToRepresent, unsigned size)
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
    else if (input.size()>size)
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

BitVectorConstantType BitVectorOperations::getBVCTFromDec(char n)
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
        
    }

}

// a1 and a2 have to be same length, result also has to be of same length  
bool BitVectorOperations::addBinArrays(const DArray<bool>& a1, const DArray<bool>& a2, DArray<bool> &result)
{
    ASS(!(a1.size()!= a2.size() || a2.size()!= result.size()));
   
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
}

BitVectorConstantType BitVectorOperations::multBVCTs(BitVectorConstantType in1, BitVectorConstantType in2)
{
    DArray<bool> a1 = in1.getBinArray();
    DArray<bool> a2 = in2.getBinArray();
    DArray<bool> previousToAdd(a1.size());
    
    for (int i = 0, j = a1.size()-1 ; i < a1.size() ; ++ i,--j )
    {
        if (a1[i] == true)
        {
            DArray<bool> curr = shiftLeft(a2,i);
             DArray<bool> sum(curr.size());
            addBinArrays(previousToAdd,curr,sum);
            previousToAdd.initFromArray(sum.size(),sum);
        }
    }
    
    BitVectorConstantType res(previousToAdd);
    return res;
}   


DArray<bool> BitVectorOperations::shiftLeft(DArray<bool> input, unsigned shiftByNum)
{
    DArray<bool> res(input.size());
    
    unsigned k;
    for (k = 0 ; k < shiftByNum ; ++k){
        res[k] = false;
    }
    
    for (unsigned i = 0 ; k< input.size(); ++k, ++i){
        res[k] = input[i];
    }
    
    return res;
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