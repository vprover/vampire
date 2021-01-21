#include "Api/Solver.hpp"

using namespace Api;

int main() {

  try{
    Solver& solver = Solver::getSolver();

    Predicate p = solver.predicate("p", 1);
    Function f = solver.function("f", 2, false);
    Term a = solver.term(solver.function("a", 0, false));

    Term faa = solver.term(f, a, a);
    Formula formula1 = solver.formula(p, a);

    Formula not_formula1 = solver.negation(formula1);
    //p(a) \/ ~p(a)
    Formula or_formula = solver.formula(Solver::AND, formula1, not_formula1);

    solver.assertFormula(or_formula);
    Result r = solver.solve();

    cout << "proof found: " << r.unsatisfiable() << endl;

    AnnotatedFormulaIterator afi = solver.formulas();
    while(afi.hasNext()){
      cout << afi.next().toString() << endl;
    }

    return 0;
  } catch (ApiException& e){
    cout<< "Exception: "<<e.msg()<<endl;
    return 1;
  } catch (Lib::UserErrorException& e){
    cout<< "Exception: "<<e.msg()<<endl;
    return 1;    
  }
}
