/**
 * @file tProgramAnalysis.cpp
 * Implements class ProgramAnalysis.
 */

#include "Test/UnitTesting.hpp"

#define UNIT_ID pgm_analysis  //the UNIT_ID must be a valid variable name
UT_CREATE;

#include "Program/Analyze.hpp"
#include "Program/Variable.hpp"
#include "Program/Expression.hpp"
#include "Program/Statement.hpp"

using namespace Program;

// void partition () { // from paper by S.Gulwani, PLDI 2006
//   int a, m, b, c;
//   int *aa, *bb;

//   //This is the program for which Vampire is ran
//   //Vampire generates invariants with quantifier alterantions
// 1   a = 0;
// 2   b = 0;
// 3   c = 0;
// 4   while ( a < m ) {
// 5     if ( aa[a] >= 0 ) {
// 6       bb[b] = aa[a];
// 7       b = b+1;
// 8     } else {
// 9       cc[c] = aa[a];
//10       c = c+1;
//11     }
//12     a = a+1;
//13   }
//14 }

TEST_FUN(canonical)
{
  Variable* va = new Variable("a",Type::integerType());
  Variable* vb = new Variable("b",Type::integerType());
  Variable* vc = new Variable("c",Type::integerType());
  Variable* vm = new Variable("m",Type::integerType());

  VariableExpression* a = new VariableExpression(va);
  VariableExpression* b = new VariableExpression(vb);
  VariableExpression* c = new VariableExpression(vc);
  VariableExpression* m = new VariableExpression(vm);

  ArrayType* arrayType = new ArrayType(Type::integerType());
  Variable* vaa = new Variable("aa",arrayType);
  Variable* vbb = new Variable("bb",arrayType);
  Variable* vcc = new Variable("cc",arrayType);

  VariableExpression* aa = new VariableExpression(vaa);
  VariableExpression* bb = new VariableExpression(vbb);
  VariableExpression* cc = new VariableExpression(vcc);

  ConstantIntegerExpression* zero = new ConstantIntegerExpression(0);
  ConstantIntegerExpression* one = new ConstantIntegerExpression(1);

  // 1   a = 0;
  Assignment* a_ASS_0 = new Assignment(a,zero);

  // 2   b = 0;
  Assignment* b_ASS_0 = new Assignment(b,zero);

  // 3   c = 0;
  Assignment* c_ASS_0 = new Assignment(c,zero);

  // (a < m) in
  // 4   while ( a < m ) {
  FunctionApplicationExpression* a_less_m = new FunctionApplicationExpression(ConstantFunctionExpression::integerLess());
  a_less_m->setArgument(0,a);
  a_less_m->setArgument(1,m);

  // aa[a]
  ArrayApplicationExpression* aa_a = new ArrayApplicationExpression(aa,a);
  // bb[b]
  ArrayApplicationExpression* bb_b = new ArrayApplicationExpression(bb,b);
  // cc[c]
  ArrayApplicationExpression* cc_c = new ArrayApplicationExpression(cc,c);

  // (a+1)
  FunctionApplicationExpression* a_plus_1 = new FunctionApplicationExpression(ConstantFunctionExpression::integerPlus());
  a_plus_1->setArgument(0,a);
  a_plus_1->setArgument(1,one);
  // (b+1)
  FunctionApplicationExpression* b_plus_1 = new FunctionApplicationExpression(ConstantFunctionExpression::integerPlus());
  b_plus_1->setArgument(0,b);
  b_plus_1->setArgument(1,one);
  // (c+1)
  FunctionApplicationExpression* c_plus_1 = new FunctionApplicationExpression(ConstantFunctionExpression::integerPlus());
  c_plus_1->setArgument(0,c);
  c_plus_1->setArgument(1,one);

  //12       a = a+1;
  Assignment* a_ASS_a_plus_1 = new Assignment(a,a_plus_1);
  // 7       b = b+1;
  Assignment* b_ASS_b_plus_1 = new Assignment(b,b_plus_1);
  //10       c = c+1;
  Assignment* c_ASS_c_plus_1 = new Assignment(c,c_plus_1);

  // 6       bb[b] = aa[a];
  Assignment* bb_b_ASS_aa_a = new Assignment(bb_b,aa_a);
  // 9       cc[c] = aa[a];
  Assignment* cc_c_ASS_aa_a = new Assignment(cc_c,aa_a);

  // 6-7  bb[b] = aa[a]; b = b+1;
  Block* thenPart = new Block(2);
  thenPart->setStatement(0,bb_b_ASS_aa_a);
  thenPart->setStatement(1,b_ASS_b_plus_1);

  // 9-10  cc[c] = aa[a]; c = c+1;
  Block* elsePart = new Block(2);
  elsePart->setStatement(0,cc_c_ASS_aa_a);
  elsePart->setStatement(1,c_ASS_c_plus_1);

  // 5-11 if-then-else
  FunctionApplicationExpression* aa_a_geq_0 = new FunctionApplicationExpression(ConstantFunctionExpression::integerGreaterEq());
  aa_a_geq_0->setArgument(0,aa_a);
  aa_a_geq_0->setArgument(1,zero);

  IfThenElse* ite = new IfThenElse(aa_a_geq_0,thenPart,elsePart);

  Block* loopBody = new Block(2);
  loopBody->setStatement(0,ite);
  loopBody->setStatement(1,a_ASS_a_plus_1);

  WhileDo* loop = new WhileDo(a_less_m,loopBody);
  // block 1-14
  Block* program = new Block(4);
  program->setStatement(0,a_ASS_0);
  program->setStatement(1,b_ASS_0);
  program->setStatement(2,c_ASS_0);
  program->setStatement(3,loop);
  cout << "\n";
  Analyze analysis(program);
  analysis.analyze();
}
