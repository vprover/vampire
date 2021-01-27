#include "Api/Solver.hpp"

using namespace Api;

int main() {

  try{
    Solver& solver = Solver::getSolver();

    solver.setTimeLimit(2);
 
    Expression ten = solver.integerConstant(10);
    Expression twenty = solver.integerConstant(20);

    Expression ten_plus_ten = solver.sum(ten, ten);

    Expression ten_plus_ten_equals_twenty = solver.equality(ten_plus_ten, twenty);

    solver.addConjecture(ten_plus_ten_equals_twenty);

    Result res = solver.solve();

    cout << "proof found: " << res.unsatisfiable() << endl;

    solver.reset();

    ten = solver.integerConstant(10);
    
    ten_plus_ten = solver.sum(ten, ten);

    ten_plus_ten_equals_twenty = solver.equality(ten_plus_ten, twenty);
    
    solver.addFormula(twenty);

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
