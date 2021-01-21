#include "Api/Solver.hpp"

using namespace Api;

int main() {

  try{
    Solver& solver = Solver::getSolver();

    solver.setTimeLimit(2);
 
    Sort realSort = solver.realSort();
    Var var_x = solver.var("X", realSort);
    Term x = solver.varTerm(var_x);
    Term ceiling_x = solver.ceiling(x);

    //ceiling(x) >= x
    Formula ceil_greater_or_equal = solver.geq(ceiling_x, x);
    Formula ceil_greater_or_equal_quanitifed = solver.formula(Solver::FORALL, var_x, ceil_greater_or_equal);

    solver.addFormula(ceil_greater_or_equal_quanitifed);

    Result res = solver.solve();

    cout << "proof found: " << res.unsatisfiable() << endl;

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
