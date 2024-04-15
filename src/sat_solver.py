#!/usr/bin/python3

from pysat.solvers import Solver
import itertools
import automata

GLOBAL_VARIABLE_COUNT = 0

class Invariant:
    def __init__(self, num_states):
        self.num_states = num_states
        self.trans_variables = list()
        self.state_variables = list()

def generate_condition_for_determinism(
        used_alphabet: list, 
        inv: Invariant,
        solver: Solver
    ):
    global GLOBAL_VARIABLE_COUNT

    if inv.num_states < 2:
        return 

    # create transition variables
    # src+symbol+dst ordered alphabetically
    inv.trans_variables = list(range(1+GLOBAL_VARIABLE_COUNT, 1+GLOBAL_VARIABLE_COUNT+inv.num_states*inv.num_states*len(used_alphabet)))
    GLOBAL_VARIABLE_COUNT += len(inv.trans_variables)

    # k possible targets for each state and symbol
    # -> math.comb(k, 2) clauses for each state and symbol
    for index_src in inv.trans_variables.copy()[::inv.num_states*len(used_alphabet)]: 
        # every new source state
        for index_symbol in range(len(used_alphabet)):
            all_variables = [index_src + index_symbol + j for j in range(inv.num_states)]
            # generate all clauses
            all_options = list(itertools.product(all_variables, repeat=2))
            for option in all_options:
                if option[0] != option[1]:
                    solver.add_clause([-(option[0]), -(option[1])])


def generate_condition_for_completeness(
        used_alphabet: list,
        inv: Invariant,
        solver: Solver
    ):
    global GLOBAL_VARIABLE_COUNT

    for index_src in inv.trans_variables.copy()[::inv.num_states*len(used_alphabet)]: 
        # every new source state
        for index_symbol in range(len(used_alphabet)):
            all_variables = [index_src + index_symbol + j for j in range(inv.num_states)]
            # generate all clauses
            solver.add_clause(all_variables)


def generate_condition_for_accepting_states(
        used_alphabet: list,
        inv: Invariant,
        solver: Solver
    ):
    global GLOBAL_VARIABLE_COUNT

    inv.state_variables = list(range(1+GLOBAL_VARIABLE_COUNT, 1+GLOBAL_VARIABLE_COUNT+inv.num_states))
    GLOBAL_VARIABLE_COUNT += len(inv.state_variables)

    # at least one accepting state
    solver.add_clause(inv.state_variables)


def find_solution(used_alphabet: list, max_k: int):
    global GLOBAL_VARIABLE_COUNT
    
    # increment number of states
    for k_aut in range(1, max_k+1):
        GLOBAL_VARIABLE_COUNT = 0
        solver_aut = Solver(name='g3')
        A = Invariant(k_aut)

        # generate conditions for invariant
        # 1) determinism
        generate_condition_for_determinism(used_alphabet, A, solver_aut)
        # 2) completeness
        generate_condition_for_completeness(used_alphabet, A, solver_aut)
        # 3) at least one accepting state
        generate_condition_for_accepting_states(used_alphabet, A, solver_aut)
        # 4) symmetry breaking
        # TODO

        # solve
        solver_aut.solve()
        for model in solver_aut.enum_models():
            print(model)
            # convert to automaton instance
            # TODO
            # check conditions
            # TODO
            # if conditions hold, generate transducer
            # TODO
            pass

        solver_aut.delete()


def convert_model_to_automaton(model: list) -> automata.Automaton:
    # TODO
    pass

if __name__ == "__main__":
    # SAT solver test
    solver = Solver(name='g3')
    # example for (x1 & !x2) | x3 <=> (x1 | x3) & (!x2 | x3)
    solver.add_clause([1, 3])
    solver.add_clause([-2, 3])
    for model in solver.enum_models():
        print(model)