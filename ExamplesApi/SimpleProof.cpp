#include "Solver.hpp"
#include <iostream>

using namespace Vampire;

int main() {

  try{
    Solver& solver = Solver::getSolver();

    Symbol p = solver.predicate("p", 1);
    Symbol f = solver.function("f", 2, false);
    Expression a = solver.term(solver.function("a", 0, false));

    Expression faa = solver.term(f, a, a);
    Expression formula1 = solver.term(p, a);

    Expression not_formula1 = solver.negation(formula1);
    //p(a) /\ ~p(a)
    Expression and_formula = solver.andFormula(formula1, not_formula1);

    solver.assertFormula(and_formula);
    
    solver.outputProblem();

    Result r = solver.solve();

    AnnotatedFormulaIterator afi = solver.formulas();
    while(afi.hasNext()){
      cout << afi.next().toString() << endl;
    }

    return 0;
  } catch (ApiException& e){
    std::cout<< "Exception: "<<e.msg()<<std::endl;
    return 1;
  }/* catch (Lib::UserErrorException& e){
    cout<< "Exception: "<<e.msg()<<endl;
    return 1;    
  }*/
}
