// Copyright 2018-2019 Petr Homola. All rights reserved.
// Use of this source code is governed by the AGPL v3.0
// that can be found in the LICENSE file.

package sat

/*
#include "solver.h"
void veci_push_lit(veci* lits, int lit) {
  int var = abs(lit)-1;
  veci_push(lits, lit > 0 ? toLit(var) : lit_neg(toLit(var)));
}
int add_clause(solver* s, veci* lits) {
  lit* begin = veci_begin(lits);
  return solver_addclause(s, begin, begin + veci_size(lits));
}
int lit_val(solver* s, int i) {
  return s->model.ptr[i] == l_True;
}
*/
import "C"

//"fmt"

func Solve(clauses [][]int) map[int]bool {
	slv := C.solver_new()
	defer C.solver_delete(slv)
	var lits C.veci
	C.veci_new(&lits)
	defer C.veci_delete(&lits)
	for _, clause := range clauses {
		C.veci_resize(&lits, 0)
		for _, lit := range clause {
			C.veci_push_lit(&lits, C.int(lit))
		}
		if C.add_clause(slv, &lits) == 0 {
			//panic("couldn't add clause")
			return nil
		}
	}
	C.solver_simplify(slv)
	//slv.verbosity = 1
	st := C.solver_solve(slv, nil, nil)
	if st == C.l_True {
		valuation := map[int]bool{}
		for i := 0; i < int(slv.model.size); i++ {
			valuation[i] = C.lit_val(slv, C.int(i)) != 0
		}
		return valuation
	} else {
		return nil
	}
}

func SolveAll(clauses [][]int, callback func(map[int]bool)) {
	for {
		val := Solve(clauses)
		if val == nil {
			break
		}
		callback(val)
		clause := []int{}
		for k, v := range val {
			if v {
				clause = append(clause, -(k + 1))
			} else {
				clause = append(clause, k+1)
			}
		}
		clauses = append(clauses, clause)
	}
}
