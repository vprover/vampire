/**
 * @file Theory.hpp
 * Defines class Theory.
 */

#ifndef __Theory__
#define __Theory__

#include <math.h>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Exception.hpp"

#include "Shell/TermAlgebra.hpp"

#include "Sorts.hpp"
#include "Term.hpp"
#include "BitVectorOperations.hpp"
#include "Lib/Environment.hpp"

namespace Kernel {

/**
 * Exception to be thrown when the requested operation cannot be performed,
 * e.g. because of overflow of a native type.
 */
class ArithmeticException : public ThrowableBase {};


class IntegerConstantType
{
public:
  static unsigned getSort() { return Sorts::SRT_INTEGER; }

  typedef int InnerType;

  IntegerConstantType() {}
  IntegerConstantType(InnerType v) : _val(v) {}
  explicit IntegerConstantType(const vstring& str);

  IntegerConstantType operator+(const IntegerConstantType& num) const;
  IntegerConstantType operator-(const IntegerConstantType& num) const;
  IntegerConstantType operator-() const;
  IntegerConstantType operator*(const IntegerConstantType& num) const;
  IntegerConstantType operator/(const IntegerConstantType& num) const;
  IntegerConstantType operator%(const IntegerConstantType& num) const;
  
  float realDivide(const IntegerConstantType& num) const { 
    if(num._val==0) throw ArithmeticException();
    return ((float)_val)/num._val; 
  }
  IntegerConstantType quotientE(const IntegerConstantType& num) const { 
    if(num._val>0) return IntegerConstantType(::floor(realDivide(num)));
    else return IntegerConstantType(::ceil(realDivide(num)));
  }
  IntegerConstantType quotientT(const IntegerConstantType& num) const { 
    return IntegerConstantType(::trunc(realDivide(num)));
  }
  IntegerConstantType quotientF(const IntegerConstantType& num) const { 
    return IntegerConstantType(::floor(realDivide(num)));
  }

  bool operator==(const IntegerConstantType& num) const;
  bool operator>(const IntegerConstantType& num) const;

  bool operator!=(const IntegerConstantType& num) const { return !((*this)==num); }
  bool operator<(const IntegerConstantType& o) const { return o>(*this); }
  bool operator>=(const IntegerConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const IntegerConstantType& o) const { return !((*this)>o); }

  InnerType toInner() const { return _val; }

  bool isZero(){ return _val==0; }
  bool isNegative(){ return _val<0; }

  static IntegerConstantType floor(RationalConstantType rat);
  static IntegerConstantType ceiling(RationalConstantType rat);

  static Comparison comparePrecedence(IntegerConstantType n1, IntegerConstantType n2);

  vstring toString() const;
private:
  InnerType _val;
};

inline
std::ostream& operator<< (ostream& out, const IntegerConstantType& val) {
  return out << val.toInner();
}


class BitVectorConstantType{
       
  
    public: 
        typedef DArray<bool> BinArray;
        BitVectorConstantType(BinArray n): binArray(n){}
        BitVectorConstantType(){};
        BitVectorConstantType(unsigned s)
        {
            DArray<bool> setTo(s);
            setBinArray(setTo);
        }
    vstring toString() const;

    unsigned size() const {return binArray.size();}
    unsigned getSortOld() const{
         //return sortB;
        return env.sorts->addBitVectorSort(binArray.size()); // this should probabyl be changed to getBitVectorSort
    
    } 
    // this function will actually not get called
    static unsigned getSort() {
        USER_ERROR("this shouldnt get called ");
    } 
    
    void setBinArray(DArray<bool> setTo)
    {
        binArray.initFromArray(setTo.size(),setTo);
    }
    
    void prepareBinArray(unsigned size)
    {
        DArray<bool> uhuh(size);
        setBinArray(uhuh);
    }
    
    DArray<bool> getBinArray() const&
    {
        return binArray;
    }
    
    bool getValueAt(unsigned index) const
    {
        return binArray[index];
    }
    
    void setValueAt(unsigned index, bool value)
    {
        binArray[index] = value;
    }
    
    /// RE
    BitVectorConstantType& operator=(const BitVectorConstantType& o)
    {
       setBinArray(o.getBinArray());
       return static_cast<BitVectorConstantType&>(*this);
    }
    bool operator==(const BitVectorConstantType& num) const;
    bool operator!=(const BitVectorConstantType& num) const;
   ///////////////////////////
    ///////////////////////////
    /////////////////////////// 
   /////////////////////////// START FUNCTIONS TO BE MOVED
 
    //add a1 and a2, and put result in a1
    static bool addBVCTs(BitVectorConstantType& a1, const BitVectorConstantType& a2)
    {
        ASS_EQ(a1.size(),a2.size());
        
        bool carry = false;
        for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
        {
            bool old = a1.getValueAt(i);
            bool val = a1.getValueAt(i)^a2.getValueAt(i)^carry;
            a1.setValueAt(i,val);
            carry = ((old && carry && !a2.getValueAt(i)) || (a2.getValueAt(i) && carry && !old) || (a2.getValueAt(i) && !carry && old) ||(a2.getValueAt(i) && carry && old));
        }

        return carry;
    }
    
    static void subtractBVCTs(BitVectorConstantType& a1, const BitVectorConstantType& a2)
    {
        ASS_EQ(a1.size(),a2.size());
        
        BitVectorConstantType arg2Notted(a1.size());
        bvnot(a2,arg2Notted);
        addBVCTs(a1,arg2Notted);
        BitVectorConstantType one = getOne(a1.size());
        addBVCTs(a1,one);
        
    }
    
   static void inplaceShiftLeft(BitVectorConstantType& in, unsigned shiftByNum)
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
    
    
    static void inPlaceShiftRight(BitVectorConstantType& input, unsigned shiftByNum)
    {
        unsigned startAt = shiftByNum;
        for (unsigned i = 0 ; i < input.size() - shiftByNum; ++i,++startAt){
            input.setValueAt(startAt - shiftByNum, input.getValueAt(startAt)); 
        }
        for (unsigned k = input.size()-1, i = 0 ; i<shiftByNum; --k,++i){
            input.setValueAt(k,false);
        }
        
    }
    
    static void inPlaceArithmeticShiftRight(BitVectorConstantType& input, unsigned shiftByNum)
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
    
    
    static bool isOne(const BitVectorConstantType& arg)
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
    
   void static printBoolArrayContent(DArray<bool> array)
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
    
    static bool isZero(const BitVectorConstantType& q)
    {
        for (int i = 0 ; i <q.size();++i){
            if (q.getValueAt(i))
                return false;
        }
        return true;
    }
    
    static BitVectorConstantType getOne(unsigned size)
    {
        DArray<bool> one(size);
        one[0] = true;
        for (int i = 1 ; i < size; ++ i){
            one[i] = false;
        }
        BitVectorConstantType res(size);
        res.setBinArray(one);
        return res;
    }
    
    static BitVectorConstantType getAllOnes(unsigned size)
    {
        DArray<bool> allOne(size);
        
        for (int i = 0 ; i < size; ++ i){
            allOne[i] = true;
        }
        BitVectorConstantType res(size);
        res.setBinArray(allOne);
        return res;
    }
     
    static BitVectorConstantType getZero(unsigned size)
    {
        BitVectorConstantType res(size);
        for (int i =0; i < size; ++i){
            res.setValueAt(i,false);
        }
        return res;
    }
    ///////////////////////////
    ///////////////////////////
    ///////////////////////////
    /////////////////////////// END FUNCTIONS TO BE MOVED
    
    static void bvneg(const BitVectorConstantType& arg, BitVectorConstantType& res)
    {
        ASS_EQ(arg.size(),res.size());
        bool encounteredOne = false;
        for (int i = 0; i<arg.size(); ++i){
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
    static void bvnot(const BitVectorConstantType& arg, BitVectorConstantType& res)
    {
        ASS_EQ(arg.size(),res.size());
        for (int i = 0; i<arg.size();++i){
            res.setValueAt(i, !arg.getValueAt(i));
        }
    }
    
    static bool bvadd(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        bool carry = false;
        for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
        {
            result.setValueAt(i,a1[i] ^ a2[i] ^ carry);
            carry = ((a1[i] && carry && !a2[i]) || (a2[i] && carry && !a1[i]) || (a2[i] && !carry && a1[i]) ||(a2[i] && carry && a1[i]));

        }

        return carry;
    }
    
    static void bvor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,a1[i] || a2[i]);
    }
    
    static void bvxor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,a1[i] ^ a2[i]);
    }
    
    static void bvnor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,!(a1[i] || a2[i]));
    }
    
    static void bvxnor(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,(a1[i] == a2[i]));
          
    }
    
    static void bvmul(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
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
    
    static void bvurem(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
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
            result = getZero(arg1.size());
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
    
    static void bvudiv(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
         //  bvudiv now returns a vector of all 1's if the second operand is 0
        //  axiom?
        if (isZero(arg2))
        {
            result = getAllOnes(arg1.size());
            return;
        }
        
        // x / 1 = x 
        // axiom?
        if (isOne(arg2))
        {
            result = arg1;
            return;
        }
        
        BitVectorConstantType one = getOne(arg1.size());
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
    
    static void bvsdiv(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
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
    static void bvsrem(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
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
    
    
    static void bvsmod(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
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
    
    
    static void bvand(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
         
        for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,a1[i] && a2[i]);
          
    }
    
    static void bvnand(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        DArray<bool> a1 = arg1.getBinArray();
        DArray<bool> a2 = arg2.getBinArray();
        
        for (int i = 0, j = a1.size() - 1 ; i < a1.size() ; ++ i, --j )
            result.setValueAt(i,!(a1[i] && a2[i]));
    }
   
    
    static void bvshl(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        result = arg1;
        for (int i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i)){
                {
                    unsigned num = pow(2,i);
                    if(num>arg1.size())
                    {    
                        result = getZero(arg1.size());
                        break;
                    }
                    inplaceShiftLeft(result,num);
                }
                
             }
        }
    }
    
    static void bvlshr(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        result = arg1;
        for (unsigned i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i))
            {
                unsigned num = pow(2,i);  
                if (num>arg1.size())
                {
                    result = getZero(arg1.size());
                    break;
                }
                inPlaceShiftRight(result,num);
             }
        }
    }
    
    static void bvashr(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        result = arg1; 
        for (int i = 0 ; i < arg2.size(); ++ i){
            if (arg2.getValueAt(i)){
                {
                    unsigned num = pow(2,i);
                    if (num>arg1.size())
                    {
                        result = getZero(arg1.size());
                        break;
                    }
                    inPlaceArithmeticShiftRight(result,num);
                }
                
             }
        }
    }
    
    static void bvsub(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(arg2.size(),result.size());
        
        BitVectorConstantType arg2Notted(arg1.size());
        bvnot(arg2,arg2Notted);
        BitVectorConstantType res(arg1.size());
        bvadd(arg1,arg2Notted,res);
        BitVectorConstantType one = getOne(arg1.size());
        bvadd(res,one,result);
        
    }
    
    static void bvcomp(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        ASS_EQ(1,result.size());
        bool areEqual = true;
        for (int i = 0 ; i < arg1.size(); ++i){
            if (arg1.getValueAt(i) != arg2.getValueAt(i))
            {
                areEqual = false;
                break;
            }
        }
        result.setValueAt(0,areEqual);
    }
    
    static void zero_extend(unsigned extendBy, const BitVectorConstantType& arg , BitVectorConstantType& result)
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
    
    static void sign_extend(unsigned extendBy, const BitVectorConstantType& arg , BitVectorConstantType& result)
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
    
    // assuming only positive integer
    static void rotate_right(IntegerConstantType in, const BitVectorConstantType& arg , BitVectorConstantType& result)
    {
        ASS_EQ(arg.size(),result.size());
        
        unsigned rotateBy = in.toInner();
        unsigned newRotateBy = rotateBy;
        if (rotateBy > arg.size())
            newRotateBy = rotateBy-arg.size();
        for (int i = 0 ; i < arg.size();++i){
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
    
    // assuming only positive integer
    static void rotate_left(IntegerConstantType in, const BitVectorConstantType& arg , BitVectorConstantType& result)
    {
        ASS_EQ(arg.size(),result.size());
        
        unsigned rotateBy = in.toInner();
        unsigned newRotateBy = rotateBy;
        if (rotateBy > arg.size())
            newRotateBy = rotateBy-arg.size();
        for (int i = 0 ; i < arg.size();++i){
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
    
    
    
    static void concat(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , BitVectorConstantType& result)
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
    
    static void extract(unsigned upper, unsigned lower, const BitVectorConstantType& in, BitVectorConstantType& result)
    {
        ASS_EQ(upper-lower+1,result.size());
        DArray<bool> resultArray(upper-lower+1);
        for (unsigned i = 0 ; i < result.size(); ++i){
            resultArray[i] = in.getValueAt(lower);
            ++lower;
        }
        result.setBinArray(resultArray);
        
    }
    
    
    static void bvule(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        
        unsigned size = arg1.size();
       
        if (arg1 == arg2)
            result = true;
        else
        {
            BitVectorConstantType arg2Notted(size);
            bvnot(arg2,arg2Notted);
            const BitVectorConstantType one = getOne(size);
            bool carry = addBVCTs(arg2Notted,arg1);
            result = !(addBVCTs(arg2Notted,one) || carry);
        }     
    }
    
    
    static void bvuge(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        
        unsigned size = arg1.size();
        BitVectorConstantType arg2Notted(size);
              
        BitVectorConstantType::bvnot(arg2,arg2Notted);
        bool carry = addBVCTs(arg2Notted, arg1);
              
        BitVectorConstantType one = getOne(size);
        result = addBVCTs(arg2Notted,one) || carry;
              
    }
    
 
    static void bvugt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        
        unsigned size = arg1.size();
        BitVectorConstantType arg2Notted(size);
        bvnot(arg2,arg2Notted);
        BitVectorConstantType one = getOne(size);
        
        bool carry = addBVCTs(arg2Notted, arg1);
        bool tempResult = addBVCTs(arg2Notted,one) || carry;
        
        if ((carry && isZero(arg2Notted)) || (tempResult && isZero(arg2Notted)))
            result = false;
        else
            result = tempResult;
    }
    //correct?
    static void bvult(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        bvugt(arg2,arg1,result);
    }
    
    
    static void bvslt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        bool check = false;
        bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
        bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
        
        if (msb_arg1 && !msb_arg2)
            check = true;
        bool check2 = false;
        if (msb_arg1 == msb_arg2)
        {
            bool temp;
            bvult(arg1,arg2,temp);
            if (temp)
                check2 = true;
        }
        result = check^check2;
        
    }
    
    
    static void bvsle(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        bool check = false;
        bool msb_arg1 = arg1.getValueAt(arg1.size()-1);
        bool msb_arg2 = arg2.getValueAt(arg2.size()-1);
        
        if (msb_arg1 && !msb_arg2)
            check = true;
        bool check2 = false;
        if (msb_arg1 == msb_arg2)
        {
            bool temp;
            bvule(arg1,arg2,temp);
            if (temp)
                check2 = true;
        }
        result = check || check2;
        
    }
    
    static void bvsgt(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        bvslt(arg2,arg1,result);
    }
    
    static void bvsge(const BitVectorConstantType& arg1, const BitVectorConstantType& arg2 , bool& result)
    {
        ASS_EQ(arg1.size(),arg2.size());
        bvsle(arg2,arg1,result);
    }
    
    
private: 
    
    BinArray binArray;
};

/**
 * A class for representing rational numbers
 *
 * The class uses IntegerConstantType to store the numerator and denominator.
 * This ensures that if there is an overflow in the operations, an exception
 * will be raised by the IntegerConstantType methods.
 */
struct RationalConstantType {
  typedef IntegerConstantType InnerType;

  static unsigned getSort() { return Sorts::SRT_RATIONAL; }

  RationalConstantType() {}

  RationalConstantType(InnerType num, InnerType den);
  RationalConstantType(const vstring& num, const vstring& den);
  RationalConstantType(InnerType num); //assuming den=1

  RationalConstantType operator+(const RationalConstantType& num) const;
  RationalConstantType operator-(const RationalConstantType& num) const;
  RationalConstantType operator-() const;
  RationalConstantType operator*(const RationalConstantType& num) const;
  RationalConstantType operator/(const RationalConstantType& num) const;

  RationalConstantType floor() const { 
    return RationalConstantType(IntegerConstantType::floor(*this));
  }
  RationalConstantType ceiling() const { 
    return RationalConstantType(IntegerConstantType::ceiling(*this));
  }
  RationalConstantType truncate() const { 
    return RationalConstantType(_num.quotientT(_den));
  }

  bool isInt() const;

  bool operator==(const RationalConstantType& num) const;
  bool operator>(const RationalConstantType& num) const;

  bool operator!=(const RationalConstantType& num) const { return !((*this)==num); }
  bool operator<(const RationalConstantType& o) const { return o>(*this); }
  bool operator>=(const RationalConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const RationalConstantType& o) const { return !((*this)>o); }

  bool isZero(){ return _num.toInner()==0; } 
  // relies on the fact that cannonize ensures that _den>=0
  bool isNegative(){ ASS(_den>=0); return _num.toInner() < 0; }

  RationalConstantType quotientE(const RationalConstantType& num) const {
    if(_num.toInner()>0 && _den.toInner()>0){
       return ((*this)/num).floor(); 
    }
    else return ((*this)/num).ceiling();
  }
  RationalConstantType quotientT(const RationalConstantType& num) const {
    return ((*this)/num).truncate();
  }
  RationalConstantType quotientF(const RationalConstantType& num) const {
    return ((*this)/num).floor(); 
  }


  vstring toString() const;

  const InnerType& numerator() const { return _num; }
  const InnerType& denominator() const { return _den; }

  static Comparison comparePrecedence(RationalConstantType n1, RationalConstantType n2);

protected:
  void init(InnerType num, InnerType den);

private:
  void cannonize();

  InnerType _num;
  InnerType _den;
};

inline
std::ostream& operator<< (ostream& out, const RationalConstantType& val) {
  return out << val.toString();
}


class RealConstantType : public RationalConstantType
{
public:
  static unsigned getSort() { return Sorts::SRT_REAL; }

  RealConstantType() {}
  explicit RealConstantType(const vstring& number);
  explicit RealConstantType(const RationalConstantType& rat) : RationalConstantType(rat) {}

  RealConstantType operator+(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator+(num)); }
  RealConstantType operator-(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator-(num)); }
  RealConstantType operator-() const
  { return RealConstantType(RationalConstantType::operator-()); }
  RealConstantType operator*(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator*(num)); }
  RealConstantType operator/(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator/(num)); }

  RealConstantType floor() const { return RealConstantType(RationalConstantType::floor()); }
  RealConstantType truncate() const { return RealConstantType(RationalConstantType::truncate()); }
  RealConstantType ceiling() const { return RealConstantType(RationalConstantType::ceiling()); }

  RealConstantType quotientE(const RealConstantType& num) const 
    { return RealConstantType(RationalConstantType::quotientE(num)); }
  RealConstantType quotientT(const RealConstantType& num) const 
    { return RealConstantType(RationalConstantType::quotientT(num)); } 
  RealConstantType quotientF(const RealConstantType& num) const 
    { return RealConstantType(RationalConstantType::quotientF(num)); }

  vstring toNiceString() const;

  static Comparison comparePrecedence(RealConstantType n1, RealConstantType n2);
private:
  static bool parseDouble(const vstring& num, RationalConstantType& res);

};

inline
std::ostream& operator<< (ostream& out, const RealConstantType& val) {
  return out << val.toString();
}


/**
 * A singleton class handling tasks related to theory symbols in Vampire
 */
class Theory
{
public:
  /**
   * Interpreted symbols and predicates
   *
   * If interpreted_evaluation is enabled, predicates GREATER_EQUAL,
   * LESS and LESS_EQUAL should not appear in the run of the
   * SaturationAlgorithm (they'll be immediately simplified by the
   * InterpretedEvaluation simplification).
   */
  enum Interpretation
  {
    //predicates

    EQUAL,

    INT_IS_INT,
    INT_IS_RAT,
    INT_IS_REAL,
    INT_GREATER,
    INT_GREATER_EQUAL,
    INT_LESS,
    INT_LESS_EQUAL,
    INT_DIVIDES,

    RAT_IS_INT,
    RAT_IS_RAT,
    RAT_IS_REAL,
    RAT_GREATER,
    RAT_GREATER_EQUAL,
    RAT_LESS,
    RAT_LESS_EQUAL,

    REAL_IS_INT,
    REAL_IS_RAT,
    REAL_IS_REAL,
    REAL_GREATER,
    REAL_GREATER_EQUAL,
    REAL_LESS,
    REAL_LESS_EQUAL,

    //numeric functions

    INT_SUCCESSOR,
    INT_UNARY_MINUS,
    INT_PLUS,  // sum in TPTP
    INT_MINUS, // difference in TPTP
    INT_MULTIPLY,
    INT_QUOTIENT_E,
    INT_QUOTIENT_T,
    INT_QUOTIENT_F,
    INT_REMAINDER_E,
    INT_REMAINDER_T,
    INT_REMAINDER_F,
    INT_FLOOR,
    INT_CEILING,
    INT_TRUNCATE,
    INT_ROUND,
    INT_ABS,

    RAT_UNARY_MINUS,
    RAT_PLUS, // sum in TPTP
    RAT_MINUS,// difference in TPTP
    RAT_MULTIPLY,
    RAT_QUOTIENT,
    RAT_QUOTIENT_E,
    RAT_QUOTIENT_T,
    RAT_QUOTIENT_F,
    RAT_REMAINDER_E,
    RAT_REMAINDER_T,
    RAT_REMAINDER_F,
    RAT_FLOOR,
    RAT_CEILING,
    RAT_TRUNCATE,
    RAT_ROUND,

    REAL_UNARY_MINUS,
    REAL_PLUS,  // plus in TPTP
    REAL_MINUS, // difference in TPTP
    REAL_MULTIPLY,
    REAL_QUOTIENT,
    REAL_QUOTIENT_E,
    REAL_QUOTIENT_T,
    REAL_QUOTIENT_F,
    REAL_REMAINDER_E,
    REAL_REMAINDER_T,
    REAL_REMAINDER_F,
    REAL_FLOOR,
    REAL_CEILING,
    REAL_TRUNCATE,
    REAL_ROUND,

    //conversion functions
    INT_TO_INT,
    INT_TO_RAT,
    INT_TO_REAL,
    RAT_TO_INT,
    RAT_TO_RAT,
    RAT_TO_REAL,
    REAL_TO_INT,
    REAL_TO_RAT,
    REAL_TO_REAL
    
    // IMPORTANT - if you add something to end of this, update it in LastNonStructuredInterepretation 
    
    //INVALID_INTERPRETATION // replaced by LastNonStructuredInterepretation
  };

  unsigned LastNonStructuredInterepretation(){ return REAL_TO_REAL; }

    /**
     * Maximal element number in the enum Interpretation
     *
     * At some points we make use of the fact that we can iterate through all
     * interpretations by going through the set {0,...,MAX_INTERPRETED_ELEMENT}.
     */
  unsigned MaxInterpretedElement(){
    return LastNonStructuredInterepretation() + _structuredSortInterpretations.size(); 
  }

  unsigned numberOfInterpretations(){
      return LastNonStructuredInterepretation() + LastStructuredInterpretation();
  }

  bool isValidInterpretation(Interpretation i){
    return i <= MaxInterpretedElement();
  }

  bool isPlus(Interpretation i){
    return i == INT_PLUS || i == RAT_PLUS || i == REAL_PLUS;
  }

 /*
  * StructuredSortInterpretations begin from the last interpretation in Interpretation
  *
  * They will be initialised as MaxInterpretedElement()+1
  *
  */


  /** enum for the kinds of StructuredSort interpretations **/
  enum class StructuredSortInterpretation
  {
    ARRAY_SELECT,
    ARRAY_BOOL_SELECT,
    ARRAY_STORE,
    // currently unused
    LIST_HEAD,
    LIST_TAIL,
    LIST_CONS,
    LIST_IS_EMPTY,
    
    BVADD,
    BVAND,
    BVASHR,
    BVCOMP,
    BVLSHR,
    BVMUL,
    BVNAND,
    BVNEG,
    BVNOR,
    BVNOT,
    BVOR,
    BVSDIV,
    BVSMOD,
    BVSGE,
    BVSGT,
    BVSHL,
    BVSREM,
    BVSLE,
    BVSLT,
    BVSUB,
    BVUDIV,
    BVULE,
    BVUGT,
    BVUGE,
    BVULT,
    BVUREM,
    BVXNOR,
    BVXOR,
    
    BV_ROTATE_LEFT,
    BV_ROTATE_RIGHT,
    BV_SIGN_EXTEND,
    BV_ZERO_EXTEND,
    CONCAT,
    EXTRACT,
    REPEAT
  };
  unsigned LastStructuredInterpretation(){
    return static_cast<unsigned>(StructuredSortInterpretation::REPEAT);
  }
  
  
  unsigned getSymbolForStructuredSort(unsigned sort, StructuredSortInterpretation interp, int arg1, int arg2);
  unsigned getSymbolForStructuredSort(unsigned sort, StructuredSortInterpretation interp);
  
  Interpretation getInterpretation(unsigned sort, StructuredSortInterpretation i){
      return getInterpretation(sort, i, -1,-1);
  }
  
  // maybe have to change this to int 
  Interpretation getInterpretation(unsigned sort, StructuredSortInterpretation i, int arg1, int arg2){
    // key = make_pair(sort, i);
    AKey key(sort, i, arg1, arg2);
    unsigned interpretation;
    if (!_structuredSortInterpretations.find(key, interpretation)) {
      interpretation = MaxInterpretedElement() + 1;
      _structuredSortInterpretations.insert(key, interpretation);
    }
    return static_cast<Interpretation>(interpretation);
  }
  
  bool isStructuredSortInterpretation(Interpretation i){
    return i > LastNonStructuredInterepretation();
  }
  unsigned getSort(Interpretation i){
    return getData(i).getResultSort();
  }

  static vstring getInterpretationName(Interpretation i);
  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);
  static bool isInequality(Interpretation i);
  static Sorts::StructuredSort getInterpretedSort(StructuredSortInterpretation ssi);
  static BaseType* getOperationType(Interpretation i);
  static BaseType* getStructuredSortOperationType(Interpretation i);
  static bool hasSingleSort(Interpretation i);
  static unsigned getOperationSort(Interpretation i);
  static bool isConversionOperation(Interpretation i);
  static bool isLinearOperation(Interpretation i);
  static bool isNonLinearOperation(Interpretation i);

  static bool isArrayOperation(Interpretation i);
  static unsigned getArrayOperationSort(Interpretation i);
  static unsigned getArrayDomainSort(Interpretation i);
  
  static bool isBitVectorOperation(Interpretation i);
  static unsigned getBitVectorArg1Sort(Interpretation i );
  static unsigned getBitVectorArg2Sort(Interpretation i );
  
  

  unsigned getArrayExtSkolemFunction(unsigned i);
    
  static Theory theory_obj;
  static Theory* instance();

  void defineTupleTermAlgebra(unsigned arity, unsigned* sorts);

  bool isInterpretedConstant(unsigned func);
  bool isInterpretedConstant(Term* t);
  bool isInterpretedConstant(TermList t);
  bool isInterpretedNumber(TermList t);

  bool isInterpretedPredicate(unsigned pred);
  bool isInterpretedPredicate(Literal* lit);
  bool isInterpretedPredicate(Literal* lit, Interpretation itp);

  bool isInterpretedFunction(unsigned func);
  bool isInterpretedFunction(Term* t);
  bool isInterpretedFunction(TermList t);
  bool isInterpretedFunction(Term* t, Interpretation itp);
  bool isInterpretedFunction(TermList t, Interpretation itp);

  Interpretation interpretFunction(unsigned func);
  Interpretation interpretFunction(Term* t);
  Interpretation interpretFunction(TermList t);
  Interpretation interpretPredicate(unsigned pred);
  Interpretation interpretPredicate(Literal* t);

  unsigned getFnNum(Interpretation itp);
  unsigned getPredNum(Interpretation itp);

  void registerLaTeXPredName(unsigned func, bool polarity, vstring temp);
  void registerLaTeXFuncName(unsigned func, vstring temp);
  vstring tryGetInterpretedLaTeXName(unsigned func, bool pred,bool polarity=true);
  
private:
  // For recording the templates for predicate and function symbols
  DHMap<unsigned,vstring> _predLaTeXnamesPos;
  DHMap<unsigned,vstring> _predLaTeXnamesNeg;
  DHMap<unsigned,vstring> _funcLaTeXnames;

public:

  Term* fun1(Interpretation itp, TermList arg);
  Term* fun2(Interpretation itp, TermList arg1, TermList arg2);
  Term* fun3(Interpretation itp, TermList arg1, TermList arg2, TermList arg3);
  Literal* pred2(Interpretation itp, bool polarity, TermList arg1, TermList arg2);

  
  bool tryInterpretConstant(TermList trm, BitVectorConstantType& res)
  {
      CALL("Theory::tryInterpretConstant(TermList,BitVectorConstantType)");
      
      if (!trm.isTerm()) {
        return false;
      }
      return tryInterpretConstant(trm.term(),res);
  }
  
  bool tryInterpretConstant(const Term* t, BitVectorConstantType& res);
  
  
  /**
   * Try to interpret the term list as an integer constant. If it is an
   * integer constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, IntegerConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,IntegerConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, IntegerConstantType& res);
  /**
   * Try to interpret the term list as an rational constant. If it is an
   * rational constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, RationalConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,RationalConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, RationalConstantType& res);
  /**
   * Try to interpret the term list as an real constant. If it is an
   * real constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, RealConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,RealConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, RealConstantType& res);

  class AKey {
  public:
    
    AKey(){}
    AKey(unsigned resultSort, Theory::StructuredSortInterpretation ssi,  unsigned arg1, unsigned arg2):
    _ssi(ssi), _resultSort(resultSort), _arg1(arg1), _arg2(arg2)
    {
        
    }
    /*AKey(Theory::StructuredSortInterpretation ssi,  unsigned resultSort):
    _ssi(ssi), _resultSort(resultSort), _arg1(-1), _arg2(-1)
    {
        
    }*/
  AKey& operator=(const AKey& o){
		(*this)._resultSort = o._resultSort;
		(*this)._arg1 = o._arg1;
                (*this)._arg2 = o._arg2;
                (*this)._ssi = o._ssi;
		return static_cast<AKey&>(*this);
	}
  bool operator==(const AKey& o) const {
		return ((*this)._resultSort == o._resultSort && (*this)._ssi == o._ssi 
                        && (*this)._arg1 == o._arg1 && (*this)._arg2 == o._arg2) ;
	}
  bool operator!=(const AKey& o) const {
		return (!((*this)._resultSort == o._resultSort && (*this)._ssi == o._ssi 
                        && (*this)._arg1 == o._arg1 && (*this)._arg2 == o._arg2)) ;
	}
  unsigned getResultSort(){
      return _resultSort;
  }
  int getArg1(){
      return _arg1;
  }
  int getArg2(){
      return _arg2;
  }
  
  StructuredSortInterpretation getSSI(){
      return _ssi;
  }
  private:
      StructuredSortInterpretation _ssi;
      unsigned _resultSort;
      int _arg1;
      int _arg2;
      
  };
  
  
  Term* representConstant(const IntegerConstantType& num);
  Term* representConstant(const RationalConstantType& num);
  Term* representConstant(const RealConstantType& num);
  Term* representConstant(const BitVectorConstantType& num);

  Term* representIntegerConstant(vstring str);
  Term* representRealConstant(vstring str);
private:
  Theory();
  static FunctionType* getConversionOperationType(Interpretation i);

  DHMap<unsigned,unsigned> _arraySkolemFunctions;

public:
  unsigned getStructuredOperationSort(Interpretation i){
    return getData(i).getResultSort();
  }
  StructuredSortInterpretation convertToStructured(Interpretation i){
    return getData(i).getSSI();
  }
private:    
    AKey getData(Interpretation i){
    ASS(isStructuredSortInterpretation(i));
    auto it = _structuredSortInterpretations.items();
    while(it.hasNext()){
      auto entry = it.next();
      if(entry.second==i) return entry.first;
    }
    ASSERTION_VIOLATION;
  }

  DHMap<AKey,unsigned> _structuredSortInterpretations;

  
public:
  class Tuples {
  public:
    bool isFunctor(unsigned functor);
    unsigned getFunctor(unsigned arity, unsigned sorts[]);
    unsigned getFunctor(unsigned tupleSort);
    unsigned getProjectionFunctor(unsigned proj, unsigned tupleSort);
    bool findProjection(unsigned projFunctor, bool isPredicate, unsigned &proj);
  };

  static Theory::Tuples tuples_obj;
  static Theory::Tuples* tuples();
};

typedef Theory::Interpretation Interpretation;

/**
 * Pointer to the singleton Theory instance
 */
extern Theory* theory;

}

#endif // __Theory__
