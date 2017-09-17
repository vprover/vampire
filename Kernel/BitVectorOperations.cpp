
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

 
 void BitVectorOperations::inPlaceShiftRight(BitVectorConstantType& input, unsigned shiftByNum)
    {
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
    ASS(arg1.size()>0);
    
    BitVectorConstantType t(arg1.getBinArray());
    inplaceShiftLeft(arg1,1);
    inplaceShiftLeft(t,3);
    addBVCTs(arg1,t);
}  

BitVectorConstantType BitVectorOperations::getZeroBVCT(unsigned size)
 {
    BitVectorConstantType res(size);
    for (int i =0; i < size; ++i){
        res.setValueAt(i,false);
    }
        return res;
 }
  
  
  BitVectorConstantType BitVectorOperations::getOneBVCT(unsigned size)
    {
        BitVectorConstantType res(size);
        res.setValueAt(0,true);
        for (int i =1; i < size; ++i){
            res.setValueAt(i,false);
        }
        return res;
    }
  
  BitVectorConstantType BitVectorOperations::getAllOnesBVCT(unsigned size)
    {
        DArray<bool> allOne(size);
        
        for (int i = 0 ; i < size; ++ i){
            allOne[i] = true;
        }
        BitVectorConstantType res(size);
        res.setBinArray(allOne);
        return res;
    }
  
   void BitVectorOperations::bvnand(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
   {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,!(a1[i] && a2[i]));
   }
   
   void BitVectorOperations::subtractBVCTs(BitVectorConstantType& a1, const BitVectorConstantType& a2)
   {
        ASS_EQ(a1.size(),a2.size());
        
        BitVectorConstantType arg2Notted(a1.size());
        bvnot(a2,arg2Notted);
        addBVCTs(a1,arg2Notted);
        BitVectorConstantType one = getOneBVCT(a1.size());
        addBVCTs(a1,one);
    }
   
   void BitVectorOperations::bvneg(const BitVectorConstantType& arg, BitVectorConstantType& res)
    {
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
        ASS_EQ(arg.size(),res.size());
        for (unsigned i = 0; i<arg.size();++i){
            res.setValueAt(i, !arg.getValueAt(i));
        }
    }
   
   bool BitVectorOperations::bvadd(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
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
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,a1[i] || a2[i]);
    }
   
   void BitVectorOperations::bvxor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,a1[i] ^ a2[i]);
    }
   
   void BitVectorOperations::bvnor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,!(a1[i] || a2[i]));
    }
   void BitVectorOperations::bvxnor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,(a1[i] == a2[i]));
    }
   void BitVectorOperations::bvmul(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        ASS(isZero(result));

        BitVectorConstantType toAdd(arg2.getBinArray());
        unsigned lastI = 0;
        for (unsigned i = 0 ; i < arg1.size() ; ++ i)
        {
            if (arg1.getValueAt(i))
            {
                unsigned diff = i - lastI;
                inplaceShiftLeft(toAdd,diff);
                addBVCTs(result,toAdd);
                lastI = i;
            }
        }
    }
   
   void BitVectorOperations::bvurem(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        //  bvurem returns its first operand if the second operand is 0
        if (isZero(arg2))
        {
            result = arg1;
            return;
        }
        
        // if arg2 is one, there will be no remainder 
        if (isOne(arg2))
        {
            result = getZeroBVCT(arg1.size());
            return;
        }
        
        result = arg1;
        bool done = false;
        
        while (!done)
        {
            bvult(result,arg2,done);
            if(done)
                break;
            subtractBVCTs(result,arg2);
        }
    }
   
   void BitVectorOperations::bvudiv(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
         //  bvudiv now returns a vector of all 1's if the second operand is 0
        //  axiom?
        if (isZero(arg2))
        {
            result = getAllOnesBVCT(arg1.size());
            return;
        }
        
        // x / 1 = x 
        // axiom?
        if (isOne(arg2))
        {
            result = arg1;
            return;
        }
        
        BitVectorConstantType one = getOneBVCT(arg1.size());
        BitVectorConstantType workWith;
        workWith = arg1;
        bool done = false;
        
        while (!done)
        {
            bvult(workWith,arg2,done);
            if(done)
                break;
            subtractBVCTs(workWith,arg2);
            addBVCTs(result,one);
        }
        
    }
   
   void BitVectorOperations::bvsdiv(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
        bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
        if (!msb_arg1 && !msb_arg2)
        {
            bvudiv(arg1,arg2,result);
            return;
        }
        if (msb_arg1 && !msb_arg2)
        {
            BitVectorConstantType arg1Negated(arg1.size());
            bvneg(arg1,arg1Negated);
            
            BitVectorConstantType div(arg1.size());
            bvudiv(arg1Negated,arg2,div);
            bvneg(div,result);
            return;
        }
        if (!msb_arg1 && msb_arg2)
        {
            BitVectorConstantType arg2Negated(arg2.size());
            BitVectorConstantType div(arg1.size());
            bvudiv(arg1,arg2Negated,div);
            bvneg(div,result);
            return;
        }
        // negated both and do a bvudiv
        BitVectorConstantType arg1Negated(arg1.size());
        BitVectorConstantType arg2Negated(arg2.size());
        bvneg(arg1,arg1Negated);
        bvneg(arg2,arg2Negated);
        bvudiv(arg1Negated,arg2Negated,result);
        
    }
   
   void BitVectorOperations::bvsrem(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
        bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
        
        if (!msb_arg1 && !msb_arg2)
        {
            bvurem(arg1,arg2,result);
            return;
        }
        
        if (msb_arg1 && !msb_arg2)
        {
            BitVectorConstantType arg1Negated(arg1.size());
            bvneg(arg1,arg1Negated);
            BitVectorConstantType rem(arg1.size());
            bvurem(arg1Negated,arg2,rem);
            bvneg(rem,result);
            return;
        }
        
        if (!msb_arg1 && msb_arg2)
        {
            BitVectorConstantType arg2Negated(arg1.size());
            bvneg(arg2,arg2Negated);
            bvurem(arg1,arg2Negated,result);
            return;
        }
        
        BitVectorConstantType arg1Negated(arg1.size());
        BitVectorConstantType arg2Negated(arg2.size());
        bvneg(arg1,arg1Negated);
        bvneg(arg2,arg2Negated);
        
        BitVectorConstantType rem(arg2.size());
        bvurem(arg1Negated,arg2Negated,rem);
        
        bvneg(rem,result);
    }
   
   void BitVectorOperations::bvsmod(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
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
        bvurem(arg1Abs,arg2Abs,u);
        
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
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
         
        for (unsigned i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,a1[i] && a2[i]);
          
    }
   
   void BitVectorOperations::bvshl(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        
         // use log base 2 eg logbase2 size of bitvector
        result = arg1;
        double sum = 0;
        unsigned terminateIndex = (unsigned)(ceil(log2(arg2.size())));
        for (unsigned i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i)){
                {
                    double numL = pow(2,i); // 
                    sum+=numL;
                    if(numL>=arg1.size() || sum>=arg1.size() || i>=terminateIndex)
                    {    
                        result = getZeroBVCT(arg1.size());
                        break;
                    }
                    unsigned num = static_cast<unsigned>(numL);
                    inplaceShiftLeft(result,num);
                }
                
             }
        }
    }
   
   void BitVectorOperations::bvlshr(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        result = arg1;
        double sum = 0;
        unsigned terminateIndex = (unsigned)(ceil(log2(arg2.size())));
        for (unsigned i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i))
            {
                double numL = pow(2,i); 
                sum+=numL;
                if (numL>=arg1.size() || sum>=arg1.size() || i>=terminateIndex)
                {
                    result = getZeroBVCT(arg1.size());
                    break;
                }
                unsigned num = static_cast<unsigned>(numL);
                inPlaceShiftRight(result,num);
             }
        }
    }
   
   void BitVectorOperations::bvashr(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        result = arg1;
        double sum = 0;
        unsigned terminateIndex = (unsigned)(ceil(log2(arg2.size())));
        for (unsigned i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i)){
                {
                    double numL = pow(2,i); 
                    sum+=numL;
                    if (numL>=arg1.size() || sum>=arg1.size() || i>=terminateIndex)
                    {
                        result = getZeroBVCT(arg1.size());
                        break;
                    }
                    unsigned num = static_cast<unsigned>(numL);
                    inPlaceArithmeticShiftRight(result,num);
                }
                
             }
        }
    }
   
   void BitVectorOperations::bvsub(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
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
   
   void BitVectorOperations::sign_extend(unsigned extendBy, const BitVectorConstantType& arg , BitVectorConstantType& result)
    {
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
        ASS_EQ(arg1.size(),arg2.size());
        bvugt(arg2,arg1,result);
    }
   
   void BitVectorOperations::bvslt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
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
        ASS_EQ(arg1.size(),arg2.size());
        bvslt(arg2,arg1,result);
    }
   
   void BitVectorOperations::bvsge(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        bvsle(arg2,arg1,result);
    }

}
