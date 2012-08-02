#!/usr/bin/python

postfix = []
temp = []
operator = -10
operand = -20
leftparentheses = -30
rightparentheses = -40
space = -50

#convert a string into usable tokens
def strToTokens(str):
    strArr = []
    strArr = str
    tempStr = ''
    tokens = []
    tokens_index = 0
    count = 0
    for x in strArr:
        count = count+1
        if typeof(x) == operand:
            tempStr += x
        if typeof(x) == space: 
            tokens.append(tempStr)
            tokens_index = tokens_index + 1
            tempStr = ''
        if( typeof(x)== operator or x == ")" or x == "("):
            if(tempStr != ''):
                tokens.append(tempStr)
                tokens_index = tokens_index+1
                #tempStr = ''
            tempStr=''
            tokens.append(x)
            tokens_index = tokens_index+1
        if(count == len(strArr)):
            if(tempStr != ''):
                tokens.append(tempStr)
    return (tokens)

#return the top of the stack
def topStack(stack):
    return stack[len(stack)-1]
#return the top of the stack, but also pop that element
def pop_stack(stack):
    return stack.pop()
#check if the open paranthesis match the closed ones
def balanceParanthesis(string):
    count = 0
    for x in string: 
        if x == '(': 
            count = count + 1
        elif x == ')':
            count = count - 1
        else: 
            continue
    return count
#find the position of value in strin - returns -1 if it doesn't find it 
def FIND(value, strin):
    try:
        i = strin.index(value)
    except ValueError: 
        i = -1 
    return i
#checks if a token is of array type 
#this is a rather naive implementation - chechs if a operand is followed by paranthesis
#this function is needed in order to make the difference between the array type and normal 
#open and closed paranthesis
def isArray(x, string):
    if typeof(x)== operator or x =='(' or x==')': 
        return False
    fin = FIND(x, string) 
    if fin == -1 :
        return False
    elif fin+1 < len(string) and string[fin+1] == '(':
        return True
    else: return False

#the this actually create the expression string to be outputed
def evaluate(str):
    operands = []
    for x in reversed(str):
        if x == '':
            continue
        if isArray(x, str) == True:
            #in case the operand is an array treat it more carefull
            op = pop_stack(operands)
            operands.append(x+"["+op+"]")
        else:
            if typeof(x) == operand :
                operands.append(x)
            elif typeof(x) == operator and x =='#':
                # '#' is a special case of operator - it stands for unary minus
                op = pop_stack(operands)
                operands.append("("+x + op+")")
            elif typeof(x) == operator and x == "~":
                # '~' special case of operator: stands for logical negation
                op = pop_stack(operands)
                operands.append(x+op)
            elif typeof(x) == operator:
                #this happens for the binary operators
                op1 = pop_stack(operands)
                op2 = pop_stack(operands)
                operands.append('('+op1 + x + op2+')')
            else : 
                continue
    #after the evaluation is done, all that we have on the stack is the expression to be written
    return pop_stack(operands)
        
#defines the types of tokens
def typeof(s):
    if s is '(':
        return leftparentheses
    elif s is ')':
        return rightparentheses
    elif s is '+' or s is '-' or s is '*' or s is '~' or s is '/' or s is '<' or s is '#'or s is '>':
        return operator
    elif s is ' ' or s is ',':
        return space
    else :
        return operand

#this method is just for testing purpose
def convert(strin):   
    #infix = raw_input("Enter the infix notation : ")
    print strin
    print "deasupra e ce am primit "
    tem = strin[0].strip("\n")
    strin = []
    if balanceParanthesis(tem) != 0 :
        print "There are unbalanced paranthesis "
        exit(-1)
    else: 
        infix = strToTokens(tem)
        final = []
        final.append(evaluate(infix))
        print "len of final", len(final)
        return final
        #print "final expression", final

def convertS(String):
    returnV =[]
    for x in String:
        try:
            temp = x.strip("\n")
            if balanceParanthesis(temp) !=0 :
                print "Therea are unbalanced paranthesis!"
                exit(-1)
            else:
                if x.find("!=")!=-1:
                    spl = x.split("!=")
                    lhs = evaluate(strToTokens(spl[0]))
                    rhs = evaluate(strToTokens(spl[1]))
                    lhs = lhs + "!=" + rhs
                    returnV.append(lhs)
                elif x.find("=")!=-1:
                    spl = x.split("=")
                    lhs = evaluate(strToTokens(spl[0]))
                    rhs = evaluate(strToTokens(spl[1]))
                    lhs = lhs + "==" + rhs
                    returnV.append(lhs)
                else:
                    infix = strToTokens(temp)
                    returnV.append(evaluate(infix))
        except e: 
            print e
            
    #print returnV
    return returnV

if __name__ == "__main__":
    infix = raw_input("enter infix notation:")
    print "final ", convert(infix)
