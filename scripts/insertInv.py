#!/usr/bin/python 
import os 
import sys
import re 
import string 
import infXpostFx

def split_line(line):
    # return a tuple (loop invariant) , (![...] and the rest)                                                                                                                
    s= line.split(",",1)
    s1 = s[1].strip("\n")
    s1 = s1.replace(").","")
    #print s                                                                                                                                                                 
    return (s[0],s1)

def swap(str): # swaps the postitions ( eg: X2 : integer => integer X2 )                                                                                                  
    part1 = str[0]
    spl = part1.split(" ",2); # splitted[2] is the part which interests us!                                                                                                   
    splitted = spl[2].split(","); # split in individual groups eg X21:$int
    outputF = ''
    for j in range(len(splitted)):
        lhs = splitted[j].split(":") #split each group
        splitted[j] = lhs[1]+" "+lhs[0]
        if j < len(splitted)-1:
            outputF = outputF + splitted[j] +","
        else: 
            outputF = outputF + splitted[j]
    outputF =spl[1] + outputF + ";" #add the semicolons after the quantification
    return outputF

#introduce the correct negation sign ( aka replace ~ with !) 
def introduceNegation(str):
    str= str.replace("~","!")
    return str
#check if the number of open paranthesis is equal with the closed ones
def balance_paranthesis(string):
    res = 0
    for x in string:
        if x=="(":
            res = res+1
        if x==")":
            res = res-1
    return res
#replace the | with it's or correspondance || and the & with &&
#after this step, get rid of the sG functions ( just remove them from the invariant)
def introduceORAND(str):
    afterOR = str.replace("|","||")
    afterAND = afterOR.replace("&","&&")
    afterS = afterOR.split("||")
    final=""
    #remove the sG*
    for x in afterS:
        #final = final +x+ "||"
        if x.find("sG")==-1:
            final=final+x+"||"
    final = final.strip("||")
    if balance_paranthesis(final)!=0:
        final = final+")"
    final = final.replace("#","-")
    return final

def replaceConnectives(string):
    afterNeg = introduceNegation(string)
    final = introduceORAND(afterNeg)
    return final

#quantify the variables needed to be quantified, 
#and also translate the invariant into the syntax for FramaC - call for the other package
## infXpostFx.convertS(string)
def quantify(line):
   # replace the ![X..] with \forall and for each variable define the type eg:                                                                                               
   # \forall integer X1                                                                                                                                                      
   firstStep = line.split("]:",1);
   #in case the invariant has no quantified variables, return the invariant                                                                                                  
   if len(firstStep) == 1:
       tempSplit = firstStep[0].split("|")
       final = infXpostFx.convertS(tempSplit)
       FIN = ''
       for x in final: 
           FIN = FIN + x + '|'
       FIN = FIN.strip('|')
       final = []
       final.append(FIN)
       return final
   else: #the other case: ![..]:invariant                                                                                                                                    
     forall = firstStep[0]
     forall = forall.replace("![","\\forall ")
     integers = forall
     integers = integers.replace("$int","integer")
     temp = firstStep[1].strip("\n")
     temp = temp[:-1]
     temp = temp.replace("(","",1)
     spl = temp.split('|')
     temp = []
     temp = infXpostFx.convertS(spl)
     finInv = ''
     for x in temp: 
         finInv = finInv + "|" + x
     finInv = finInv.strip("|")
     return (integers,finInv)

def ensure_dir(name):
    d = os.path.dirname(name)
    if not os.path.exists(d):
        os.makedirs(d)

#create the actual invariant list which has to be printed in the C file
def work(lines):                                                                                                                                                             
    done= False      
    i=0                                                                                                                                                                      
    linv = ["/*@ \n"]
    while not done:
        finalInv=""
        try:        
            l1 = split_line(lines[i])
            l2 = quantify(l1[1]) # position two is the actual invariant                                                                                                      
            if len(l2)==1:
                conn = replaceConnectives(l2[0].strip("\n"))
                finalInv = l1[0] + " " + conn + ";\n"
            else:                    
                l3 = swap(l2)
                conn = replaceConnectives(l2[1].strip("\n"))
                finalInv = l1[0]+ "\f" + l3 + conn + ";\n" #l2[1].strip("\n") +";\n"                                                                       
                finalInv = finalInv.replace("<","<=")
                finalInv = finalInv.replace(">",">=")
            linv.append(finalInv)
            i = i + 1
        except IndexError,e:                                                                                                                                                 
            print "%s main while loop" %e                                                                                                                               
            print "tried %s records" % i                                                                                                                                     
            done = True                                                                                                                                                      
    linv.append("*/\n")
    return linv


#check if the number of command line arguments is correct
#arguments must be: file.c vanalyzeOutputFile outputFile
