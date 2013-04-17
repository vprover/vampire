/**
 * @file model.cpp
 * @brief Basic classes to describe a MIP model
 *
 * @author Domenico Salvagnin
 */
#if GNUMP

#include "Model.h"
#include "string.h"
#include <assert.h>
#include <stdio.h>
#include <iostream>
#include <iomanip>
#include <cmath>

#define INFBOUND          1e20

#define SOL_MAX_LINELEN 1024
#define BLANK           ' '

using namespace std;

Variable::Variable(const char* _name, VarType _type, const gmpRational& _lb, const gmpRational& _ub, const gmpRational& _obj)
   : name(_name), type(_type), lb(_lb), ub(_ub), objCoef(_obj) {}

bool Variable::checkBounds(const gmpRational& boundTolerance) const
{
   gmpRational relaxedLb(lb);
   relaxedLb -= boundTolerance; 
   gmpRational relaxedUb(ub);
   relaxedUb += boundTolerance; 
   if( (value < relaxedLb) || (value > relaxedUb) )
   {
      std::cerr << "Failed bound check: ";
      print(std::cerr);
      std::cerr << std::endl;
      return false;
   }
   return true;
}

bool Variable::checkIntegrality(const gmpRational& intTolerance) const
{
   if( (type != CONTINUOUS) && !value.isInteger(intTolerance) )
   {
      std::cerr << "Failed integrality check: ";
      print(std::cerr);
      std::cerr << std::endl;
      return false;
   }
   return true;
}

void Variable::boundsViolation(gmpRational& boundViol) const
{
   gmpRational lbViol;
   gmpRational ubViol;
   sub(lbViol, lb, value);
   if( lbViol.isNegative() ) lbViol.toZero();
   sub(ubViol, value, ub);
   if( ubViol.isNegative() ) ubViol.toZero();
   max(boundViol, lbViol, ubViol);
}

void Variable::integralityViolation(gmpRational& intViol) const
{
   intViol.toZero();
   if( type == CONTINUOUS ) return;
   value.integralityViolation(intViol);
}
  
void Variable::print(std::ostream& out) const
{

  if(lb.toDouble() != -INFBOUND)
  {
  gmpRational a = lb;
  a.abs();
  if(lb.toDouble()<0)
   out << "(>= (+ "<< abs(a.toDouble())<<"(*  1 " << name << " ) ) 0)\n";
  else
      if(lb.toDouble()==0)
	   out << "(>= (* 1 " << name <<"  ) 0)\n";
      else
      out << "(>= (+ "<<" ( ~ " << a.toDouble() << ") (* 1 " << name << " )) 0)\n";

  }
  if(ub.toDouble() != INFBOUND)
  {
  gmpRational a = ub;
  a.abs();

  if(ub.toDouble()>0)
   out << "(>= (+  " << a.toDouble() << " (* (~ 1) " << name << " ) ) 0)\n";
  else
      if(ub.toDouble() == 0)
	  out << "(>= (* (~ 1) " << name <<") 0)\n";
	   else
	    out << "(>= (+ ( ~ " << abs(a.toDouble()) << ") (* (~ 1) " << name << " ) ) 0)\n";
  }
  /*
   out << name << " [" << lb.toString() << "," << ub.toString() << "] ";
   switch(type)
   {
      case BINARY:
         out << "binary";
         break;
      case INTEGER:
         out << "integer";
         break;
      case CONTINUOUS:
         out << "continuous";
         break;
      default:
         out << "(unknown)";
   }
   out << ". Value: " << value.toString(); 
   */
}

BaseConstraint::BaseConstraint(const char* _name, bool _redundant)
   : name(_name), type("<unknown>"), redundant(_redundant) {}

LinearConstraint::LinearConstraint(const char* _name, LinearType _lintype, const gmpRational& _lhs, const gmpRational& _rhs, bool _redundant)
   : BaseConstraint(_name, _redundant), lintype(_lintype), lhs(_lhs), rhs(_rhs)
{
   type = "<linear>";
}

void LinearConstraint::push(Variable* v, const gmpRational& c)
{
   vars.push_back(v);
   coefs.push_back(c);
}

bool LinearConstraint::check(const gmpRational& tolerance) const
{
   // compute row activity
   gmpRational relaxedLhs(lhs);
   relaxedLhs -= tolerance; 
   gmpRational relaxedRhs(rhs);
   relaxedRhs += tolerance;
   gmpRational activity;
   for( unsigned int i = 0; i < vars.size(); ++i )
      activity.addProduct(coefs[i], vars[i]->value);
   // check lhs and rhs
   if (activity < relaxedLhs || activity > relaxedRhs)
   {
      std::cerr << std::setprecision(16) << "Failed check for cons " << name << ": "
                << activity.toDouble() << " not in [" << relaxedLhs.toDouble() << "," << relaxedRhs.toDouble() << "] -- Exact wrt linear tol: " 
                << activity.toString() << " not in [" << relaxedLhs.toString() << "," << relaxedRhs.toString() << "]" 
                << std::endl;
      return false;
   }
   return true;
}

void LinearConstraint::violation(gmpRational& viol) const
{
   // compute row activity
   gmpRational activity;
   for( unsigned int i = 0; i < vars.size(); ++i )
      activity.addProduct(coefs[i], vars[i]->value);
   // check lhs and rhs
   gmpRational lhsViol;
   gmpRational rhsViol;
   sub(lhsViol, lhs, activity);
   if( lhsViol.isNegative() ) lhsViol.toZero();
   sub(rhsViol, activity, rhs);
   if( rhsViol.isNegative() ) rhsViol.toZero();
   max(viol, lhsViol, rhsViol);
}

void LinearConstraint::print(std::ostream& out) const
{
  gmpRational ab;
     switch(lintype){
         case LESS_THAN:
         {
  	   //aici trebuie sa negam coefficients
  	    if(rhs == INFBOUND || rhs == -INFBOUND)
  	    {
  	       break;
  	    }
  	   out << "( >= (+ ";

  	   for( unsigned int i = 0; i < vars.size() - 1; ++i )
  	   {
  	       out<< "(+ ";
  	       if(coefs[i].toDouble()>0)
  	       out << "(* (~ "<< coefs[i].toDouble() <<
  		    ") " << vars[i]->name << " ) ";
  		else
  		{
  		    ab = coefs[i]; ab.abs();
  		    out << "(* "<< ab.toDouble() <<
  		    " " << vars[i]->name << " ) ";
  		}
  	   }
  	   ab = coefs[vars.size()-1]; ab.abs();
  	   if(coefs[vars.size()-1].toDouble()>0)
  	    out << "(* (~ "<< ab.toDouble() <<
  		    ") " << vars[vars.size()-1]->name << " ) ";
  	    else
  	    {

  		out << "(* "<< ab.toDouble() <<
  		    " " << vars[vars.size()-1]->name << " ) ";
  	    }
  	   for( unsigned int i = 0 ; i < vars.size()-1 ; ++i)
  	     out << " )";
  	   ab  = rhs; ab.abs();
  	   if(rhs.isNegative()){
  	       ab = rhs; ab.abs();
  	       out<< "(~ "<<ab.toDouble() << ") ) 0 )";
  	   }
  	   else
  	    out<< " "<<ab.toDouble()<<" ) 0 )";

  	   break;
         }
         case GREATER_THAN:
         {
  	   if(lhs == INFBOUND || lhs == -INFBOUND)
  	       break;
  	   out << "( >= (+ ";


  	   for( unsigned int i = 0; i < vars.size() - 1; ++i )
  	   {
  	       out<< "(+ ";
  	       if(coefs[i].toDouble()<0)
  	       {
  		   ab = coefs[i]; ab.abs();
  		   out << "(* (~ "<< ab.toDouble() <<
  		    ") " << vars[i]->name << ") ";
  		}
  		else
  		{
  		    ab = coefs[i]; ab.abs();
  		    out << "(* "<< ab.toDouble() <<
  		    " " << vars[i]->name << " ) ";
  		}
  	   }

  	   if(coefs[vars.size()-1].toDouble()<0){
  	    ab = coefs[vars.size()-1]; ab.abs();
  	    out << "(* (~ "<< ab.toDouble() <<
  		    ") " << vars[vars.size()-1]->name << " ) ";
  	   }
  	    else
  	    {
  		ab = coefs[vars.size()-1]; ab.abs();
  		out << "(* "<< ab.toDouble() <<
  		    " " << vars[vars.size()-1]->name << " ) ";
  	    }
  	   for( unsigned int i = 0 ; i < vars.size()-1 ; ++i)
  	     out << " )";
  	   ab = lhs; ab.abs();
  	   if(lhs.isPositive()){

  	       out<< "(~ "<<ab.toDouble() << ") ) 0 )";
  	   }
  	   else
  	    out<< " "<<ab.toDouble()<<" ) 0 )";

  	   break;

         }
         case EQUAL:
         {
           /*if(rhs.isZero())
             out<<"( = ";
           else */
             out << "( = (+ ";

  	    for( unsigned int i = 0; i < vars.size() - 1; ++i )
  	   {
  	       out<< "(+ ";
  	       if(coefs[i].toDouble()<0)
  	       {
  		   ab = coefs[i]; ab.abs();
  		   out << "(* (~ "<< ab.toDouble() <<
  		    ") " << vars[i]->name << ") ";
  		}
  		else
  		{
  		    ab = coefs[i]; ab.abs();
  		    out << "(* "<< ab.toDouble() <<
  		    " " << vars[i]->name << " ) ";
  		}
  	   }

  	   if(coefs[vars.size()-1].toDouble()<0){
  	    ab = coefs[vars.size()-1]; ab.abs();
  	    out << "(* (~ "<< ab.toDouble() <<
  		    " ) " << vars[vars.size()-1]->name << " ) ";
  	   }
  	    else
  	    {
  		ab = coefs[vars.size()-1]; ab.abs();
  		out << "(* "<< ab.toDouble() <<
  		    " " << vars[vars.size()-1]->name << " ) ";
  	    }
  	   for( unsigned int i = 0 ; i < vars.size()-1 ; ++i)
  	     out << " )";
  	   ab = rhs; ab.abs();
  	  // if(!rhs.isZero())
  	   {
  	     if(rhs.isPositive()){
  	       ab = rhs; ab.abs();
  	       out<< "(~ "<<ab.toDouble() << ") ) 0 )";
  	     }
  	     else
  	       out<< " "<<ab.toDouble()<<" ) 0 )";
  	   }
  	 /*  else
  	     out<<") )";*/
  	   break;
         }
         default: break;
      }
  /*out << name << " " << type << ": " << lhs.toString() << " <= ";
   for( unsigned int i = 0; i < vars.size(); ++i )
   {
      out << coefs[i].toString() << " " << vars[i]->name << " ";
   }
   out << "<= " << rhs.toString();
   */
}

SOSConstraint::SOSConstraint(const char* _name, SOSType _sostype, bool _redundant)
   : BaseConstraint(_name, _redundant), sostype(_sostype)
{
   type = "<SOS>";
}

void SOSConstraint::push(Variable* v)
{
   vars.push_back(v);
}

bool SOSConstraint::check(const gmpRational& tolerance) const
{
   switch(sostype)
   {
   case TYPE_1:
      return checkType1(tolerance);
   case TYPE_2:
      return checkType2(tolerance);
   default :
      return false;
   }
   return false;
}

void SOSConstraint::violation(gmpRational& viol) const
{
   viol.toZero();
}

void SOSConstraint::print(std::ostream& out) const
{
   out << name << " " << type;
   if( sostype == TYPE_1 ) out << " 1: ";
   else if( sostype == TYPE_2 ) out << " 2: ";
   for( unsigned int i = 0; i < vars.size(); ++i )
   {
      out << vars[i]->name << " ";
   }
}

bool SOSConstraint::checkType1(const gmpRational& tolerance) const
{
   int cnt = 0;
   gmpRational lb;
   gmpRational ub;
   lb -= tolerance;
   ub += tolerance;
   // count number of non-zero variables
   for( unsigned int i = 0; i < vars.size(); ++i )
   {
      if((vars[i]->value < lb) || (vars[i]->value > ub))
         cnt++;
   }
   return (cnt <= 1);
}

bool SOSConstraint::checkType2(const gmpRational& tolerance) const
{
   int cnt = 0;
   gmpRational lb;
   gmpRational ub;
   lb -= tolerance;
   ub += tolerance;
   const unsigned int noIndex = -1;
   unsigned int firstIndex = noIndex;
   // count number of non-zero variables
   for( unsigned int i = 0; i < vars.size(); ++i )
   {
      if((vars[i]->value < lb) || (vars[i]->value > ub))
      {
         cnt++;
         if( firstIndex == noIndex)
            firstIndex = i;
      }
   }
   if( cnt > 2 )
      return false;
   if( cnt < 2 )
      return true;
   // check if var in position (firstIndex + 1) is non-zero
   if((vars[firstIndex + 1]->value < lb) || (vars[firstIndex + 1]->value > ub))
      return true;
   return false;
}

Model::Model() : objSense(MINIMIZE), hasObjectiveValue(false) {}

Model::~Model()
{
   // delete constraints
   std::map<std::string, BaseConstraint*>::iterator citr = conss.begin();
   std::map<std::string, BaseConstraint*>::iterator cend = conss.end();
   while( citr != cend )
   {
      delete citr->second;
      ++citr;
   }
   conss.clear();
   
   // delete vars
   std::map<std::string, Variable*>::iterator vitr = vars.begin();
   std::map<std::string, Variable*>::iterator vend = vars.end();
   while( vitr != vend )
   {
      delete vitr->second;
      ++vitr;
   }
   vars.clear();
}

Variable* Model::getVar(const char* name) const
{
   std::map<std::string, Variable*>::const_iterator itr = vars.find(name);
   if( itr != vars.end() ) return itr->second;
   return NULL;
}

BaseConstraint* Model::getCons(const char* name) const
{
   std::map<std::string, BaseConstraint*>::const_iterator itr = conss.find(name);
   if( itr != conss.end() ) return itr->second;
   return NULL;
}

void Model::pushVar(Variable* var)
{
   assert ( var != NULL );
   vars[var->name] = var;
}

void Model::pushCons(BaseConstraint* cons)
{
   assert ( cons != NULL );
   conss[cons->name] = cons;
}

unsigned int Model::numVars() const
{
   return vars.size();
}
   
unsigned int Model::numConss() const
{
   return conss.size();
}
   
bool Model::readSol(const char* filename)
{
   assert( filename != NULL );
   char buf[SOL_MAX_LINELEN];
   
   FILE* fp = fopen(filename, "r");
   if( fp == NULL )
   {
      std::cerr << "cannot open file <" << filename << "> for reading" << std::endl;
      return false;
   }
   
   hasObjectiveValue = false;
   bool hasVarValue = false;
   bool isSolFeas = true;

   while(true)
   {
      // clear buffer content
      memset((void*)buf, 0, SOL_MAX_LINELEN);
      if (NULL == fgets(buf, sizeof(buf), fp))
         break;
      
      // Normalize white spaces in line
      unsigned int len = strlen(buf);
      for( unsigned int i = 0; i < len; i++ )
         if( (buf[i] == '\t') || (buf[i] == '\n') || (buf[i] == '\r') )
            buf[i] = BLANK;
      
      // tokenize
      char* nexttok;
      const char* varname = strtok_r(&buf[0], " ", &nexttok);
      if( varname == NULL )
         continue;

      if( strcmp(varname, "=infeas=") == 0 )
      {
         isSolFeas = false;
         break;
      }

      const char* valuep = strtok_r(NULL, " ", &nexttok);
      assert( valuep != NULL );

      if( strcmp(varname, "=obj=") == 0 )
      {
         // read objective value
         hasObjectiveValue = true;
         objectiveValue.fromString(valuep); 
      }
      else
      {
         // read variable value
         Variable* var = getVar(varname);
         if( var == NULL ) std::cerr << "unexpected variable<" << varname << "> in solution file" << std::endl;
         assert( var != NULL );
         gmpRational value;
         value.fromString(valuep);
         var->value = value;
         hasVarValue = true;
      }
   }
   isSolFeas = isSolFeas && hasVarValue;
   
   fclose(fp);
   fp = NULL;

   return isSolFeas;
}

void Model::check(
   const gmpRational& intTolerance,
   const gmpRational& linearTolerance,
   bool& intFeasible,
   bool& linearFeasible,
   bool& correctObj) const
{
   // check vars first
   intFeasible = true;
   linearFeasible = true;
   std::map<std::string, Variable*>::const_iterator vitr = vars.begin();
   std::map<std::string, Variable*>::const_iterator vend = vars.end();
   while( vitr != vend && intFeasible && linearFeasible )
   {
      linearFeasible &= vitr->second->checkBounds(linearTolerance);
      intFeasible &= vitr->second->checkIntegrality(intTolerance);
      ++vitr;
   }
   
   // then check constraints
   std::map<std::string, BaseConstraint*>::const_iterator citr = conss.begin();
   std::map<std::string, BaseConstraint*>::const_iterator cend = conss.end();
   while( citr != cend && linearFeasible )
   {
      linearFeasible &= citr->second->check(linearTolerance);
      ++citr;
   }

   correctObj = true;
   // then check objective function
   if( hasObjectiveValue )
   {
      gmpRational objVal;
      bool isMIP = false;
      
      vitr = vars.begin();
      while( vitr != vend )
      {
         objVal.addProduct(vitr->second->objCoef, vitr->second->value);
         if( vitr->second->type == Variable::CONTINUOUS ) isMIP = true;
         ++vitr;
      }
      gmpRational diff;
      sub(diff, objVal, objectiveValue);
      diff.abs();
      if( diff > linearTolerance )
      {
         // try a relative error of 10^-7
         gmpRational one(1, 1);
         gmpRational relTol(1, 10000000);
         gmpRational magnitude(objVal);
         gmpRational relErr;
         magnitude.abs();
         max(magnitude, one, magnitude);
         div(relErr, diff, magnitude);
         if( relErr > relTol )
         {
            correctObj = false;
            
            std::cerr << std::setprecision(16) << "Failed objective value check: " 
                      << objectiveValue.toDouble() << " != " << objVal.toDouble() << " -- Exact absolute diff: "  
                      << diff.toString() << " > " << linearTolerance.toString() << ", exact relative diff " << relErr.toString() << " > " << relTol.toString()
                      << std::endl;
         }
         else correctObj = true;
      }
   }
   else
   {
      std::cerr << "Failed objective value check: No objective value given" 
                << std::endl;
      correctObj = false;
   }
}

void Model::maxViolations(
   gmpRational& intViol,
   gmpRational& linearViol,
   gmpRational& objViol) const
{
   // check vars first
   intViol.toZero();
   linearViol.toZero();
   objViol.toZero();
   std::map<std::string, Variable*>::const_iterator vitr = vars.begin();
   std::map<std::string, Variable*>::const_iterator vend = vars.end();
   while( vitr != vend )
   {
      gmpRational viol;
      vitr->second->boundsViolation(viol);
      max(linearViol, viol, linearViol);
      vitr->second->integralityViolation(viol);
      max(intViol, viol, intViol);
      ++vitr;
   }
   // then check constraints
   std::map<std::string, BaseConstraint*>::const_iterator citr = conss.begin();
   std::map<std::string, BaseConstraint*>::const_iterator cend = conss.end();
   while( citr != cend )
   {
      gmpRational viol;
      citr->second->violation(viol);
      max(linearViol, viol, linearViol);
      ++citr;
   }
   // check objective
   if( hasObjectiveValue )
   {
      gmpRational objVal;
      vitr = vars.begin();
      while( vitr != vend )
      {
         objVal.addProduct(vitr->second->objCoef, vitr->second->value);
         ++vitr;
      }
      sub(objViol, objVal, objectiveValue);
      objViol.abs();
   }
}

void Model::checkWrtExact(
   const std::string& solverStatus,
   const std::string& exactStatus,
   const gmpRational& exactObjVal,
   const gmpRational& linearTolerance,
   bool& feasibility,
   bool& objective) const
{
   feasibility = true;
   objective = true;
   if( solverStatus == "unknown" ) return;
   if( solverStatus == "stopped" )
   {
      if( exactStatus == "infeasible" ) std::cerr << "Warning: exactStatus says infeasible but we have a solution" << std::endl;
      return;
   }
   // we are in the case solverStatus == "solved"
   if( exactStatus == "infeasible" ) feasibility = false;
   // now we can check the objective value
   if( hasObjectiveValue )
   {
      gmpRational objVal;
      bool isMIP = false;
      
      std::map<std::string, Variable*>::const_iterator vitr = vars.begin();
      std::map<std::string, Variable*>::const_iterator vend = vars.end();
      while( vitr != vend )
      {
         if( vitr->second->type == Variable::CONTINUOUS ) isMIP = true;
         ++vitr;
      }
      gmpRational diff;
      sub(diff, exactObjVal, objectiveValue);
      diff.abs();
      if( diff > linearTolerance )
      {
         std::cerr << "Failed absolute objective value check: if this is a MIP we will try something weaker"
                   << std::endl;
         // if error is greater than 0.1 fail in any case
         gmpRational maxAbsDiff(1, 10);
         if( diff > maxAbsDiff ) objective = false;
         else
         {
            // try a relative error of 10^-7 (but only if this is not a pure integer problem!)
            gmpRational one(1, 1);
            gmpRational relErr(1, 10000000);
            gmpRational magnitude(exactObjVal);
            magnitude.abs();
            max(magnitude, one, magnitude);
            mult(relErr, magnitude, relErr);
            if( isMIP && (diff < magnitude) ) objective = true;
            else objective = false;
         }
      }
      if( !objective )
      {
         std::cerr << std::setprecision(16) << "Failed objective value check: " 
                   << objectiveValue.toDouble() << " != " << exactObjVal.toDouble() << " -- Exact absolute diff: "  
                   << diff.toString() << " > " << linearTolerance.toString() 
                   << std::endl;
      }
   }
   else
   {
      std::cerr << "Failed objective value check: No objective value given" 
                << std::endl;
      objective = false;
   }
}
#include <vector>
#include <algorithm>
#include <list>
void Model::print(std::ostream& out) const
{
   out<<" (benchmark "<<modelName<<" "<<endl;
   out<<" :source {converted from MIPLIB} "<<endl;
   out<<" :status unknown "<<endl;
   out<<" :category { industrial } "<<endl;
   out<<" :logic QF_LRA "<<endl;

   //out << objName << ": ";
   std::map<std::string, Variable*>::const_iterator vitr = vars.begin();
   std::map<std::string, Variable*>::const_iterator vend = vars.end();

   std::list<std::string> uni;

   while( vitr != vend )
   {

       uni.push_back(vitr->second->name);
     //out << ":extrafuns (( "<< vitr->second->name << " Real ))"<<endl;
      ++vitr;
   }
   //uni.push_back("MAXIMIZATION");
   uni.sort();
   uni.unique();



   for( std::list<std::string>::iterator it=uni.begin(); it!=uni.end(); ++it)
	    out << ":extrafuns (( "<< *it << " Real ))"<<endl;
   out << ":formula (and ";


   std::map<std::string, Variable*>::const_iterator vi = vars.begin();
   std::map<std::string, Variable*>::const_iterator ve = vars.end();


   unsigned int par = 0;
   out<<"(> ";
   while( vi != ve )
   {
       if(vi->second->objCoef.toDouble() != 0 && vi->second->objCoef != INFBOUND && vi->second->objCoef !=-INFBOUND)
       {
       gmpRational a = vi->second->objCoef;
       a.abs();
       out << " (+ ";
       par++;

       if(vi->second->objCoef.toDouble()<0 )
         out << " (* (~ "<< a.toDouble() <<" ) "<< vi->second->name << " ) \n";
       else
	   out << " (* "<< a.toDouble() <<"  "<< vi->second->name << " )\n";
       }
      ++vi;
   }
   for (unsigned int i=0 ; i< par ; ++i )
       out << " )";
   out <<" 0 ) "<<endl;

   std::map<std::string, BaseConstraint*>::const_iterator citr = conss.begin();
   std::map<std::string, BaseConstraint*>::const_iterator cend = conss.end();
   while( citr != cend )
   {
      citr->second->print(out);
      out << std::endl;
      ++citr;
   }

   //out<< "( > (* 1 MAXIMIZATION ) 0 )\n";
   vitr = vars.begin();
   vend = vars.end();
   while( vitr != vend )
   {
      vitr->second->print(out);
     // out << std::endl;
      ++vitr;
   }

   out << ") )";
}


/*
void Model::print(std::ostream& out) const
{
   out << "Model: " << modelName << std::endl;
   if( objSense == MINIMIZE )
      out << "Minimize ";
   else if( objSense == MAXIMIZE )
      out << "Maximize ";
      
   out << objName << ": ";
   std::map<std::string, Variable*>::const_iterator vitr = vars.begin();
   std::map<std::string, Variable*>::const_iterator vend = vars.end();
   while( vitr != vend )
   {
      out << vitr->second->objCoef.toString() << " " << vitr->second->name << " ";
      ++vitr;
   }
   out << std::endl;
   
   out << "s.t." << std::endl;
   std::map<std::string, BaseConstraint*>::const_iterator citr = conss.begin();
   std::map<std::string, BaseConstraint*>::const_iterator cend = conss.end();
   while( citr != cend )
   {
      citr->second->print(out);
      LinearConstraint* lcons = static_cast<LinearConstraint*>(citr->second);
      out<< lcons->lintype<<std::endl;
      std::vector<Variable*> variables(lcons->vars);
      std::vector<gmpRational> coef(lcons->coefs);
      std::vector<Variable*>::const_iterator varCite=variables.begin();
      std::vector<Variable*>::const_iterator varEnd =variables.end();
      for (int i = 0 ; i < variables.size() ; ++i) 
      {
	gmpRational r = variables[i]->value;
	out<<coef[i].toString()<<"*"<<variables[i]->name<<" "<<r.toString()<<std::endl;
      }
      lcons->print(out);
      
      out << std::endl;
      ++citr;
   }
   
   out << "Vars:" << std::endl;
   vitr = vars.begin();
   vend = vars.end();
   while( vitr != vend )
   {
      vitr->second->print(out);
      out << std::endl;
      ++vitr;
   }
}
*/

void Model::printSol(std::ostream& out) const
{
   out << "Solution: " << std::endl;
   std::map<std::string, Variable*>::const_iterator vitr = vars.begin();
   std::map<std::string, Variable*>::const_iterator vend = vars.end();
   while( vitr != vend )
   {
      out << vitr->second->name << " = " << vitr->second->value.toString() << std::endl;
      ++vitr;
   }
}
#endif //GNUMP

