#!/usr/bin/python3

from pysat.solvers import Solver

if __name__ == "__main__":
    # SAT solver test
    solver = Solver(name='g3')
    # example for (x1 & !x2) | x3 <=> (x1 | x3) & (!x2 | x3)
    solver.add_clause([1, 3])
    solver.add_clause([-2,3])
    for model in solver.enum_models():
        print(model)