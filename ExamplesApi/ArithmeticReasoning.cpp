#include "Api/Solver.hpp"

using namespace Api;

int main() {

  try{
    Solver& solver = Solver::getSolver();

    solver.setTimeLimit(2);
 
    Term ten = solver.integerConstant(10);
    Term twenty = solver.integerConstant(20);

    Term ten_plus_ten = solver.sum(ten, ten);

    Formula ten_plus_ten_equals_twenty = solver.equality(ten_plus_ten, twenty);

    solver.addConjecture(ten_plus_ten_equals_twenty);

    Result res = solver.solve();

    cout << "proof found: " << res.unsatisfiable() << endl;

    solver.resetHard();

    ten = solver.integerConstant(10);
    
    ten_plus_ten = solver.sum(ten, ten);

    ten_plus_ten_equals_twenty = solver.equality(ten_plus_ten, twenty);
    
    solver.addFormula(ten_plus_ten_equals_twenty);

    res = solver.solve();

    cout << "proof found: " << res.unsatisfiable() << endl;

    return 0;
  } catch (ApiException& e){
    cout<< "Exception: "<<e.msg()<<endl;
    return 1;
  } catch (Lib::UserErrorException& e){
    cout<< "Exception: "<<e.msg()<<endl;
    return 1;    
  }
}
