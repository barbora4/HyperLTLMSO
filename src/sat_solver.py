#!/usr/bin/python3

from pysat.solvers import Solver
import itertools
import automata
import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting
import invariant_conditions

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

def find_solution(
        max_k: int,
        restricted_initial_conf: automata.Automaton,
        restricted_transducer: automata.Automaton,
        original_transducer: automata.Automaton,
        accepting_transitions: automata.Automaton,
        trace_quantifiers: list,
        contains_eventually_operator: bool 
    ):
    global GLOBAL_VARIABLE_COUNT
    
    # increment number of states
    for k_aut in range(1, max_k+1):
        GLOBAL_VARIABLE_COUNT = 0
        solver_aut = Solver(name='g3')
        A = Invariant(k_aut)
        aut_alphabet = restricted_initial_conf.get_all_symbols()

        # generate conditions for invariant
        # 1) determinism
        generate_condition_for_determinism(aut_alphabet, A, solver_aut)
        # 2) completeness
        #generate_condition_for_completeness(aut_alphabet, A, solver_aut)
        # 3) at least one accepting state
        generate_condition_for_accepting_states(aut_alphabet, A, solver_aut)
        # 4) symmetry breaking
        # TODO

        # solve
        solver_aut.solve()
        for model in solver_aut.enum_models():
            # convert to automaton instance
            A_aut = convert_model_to_automaton(
                model = model, 
                used_alphabet = aut_alphabet, 
                inv = A, 
                symbol_map = restricted_initial_conf.symbol_map.copy()
            )
            # check conditions
            # 1) inclusion of initial configurations
            initial_condition_holds = invariant_conditions.check_initial_invariant_condition(
                extended_initial_aut = restricted_initial_conf,
                invariant = A_aut
            )
            if not initial_condition_holds:
                continue
            # 2) inductiveness
            is_inductive = invariant_conditions.check_invariant_inductiveness(
                invariant = A_aut,
                extended_transducer = restricted_transducer
            )
            if not is_inductive:
                continue
            
            # conditions for the invariant hold -> generate transducer
            GLOBAL_VARIABLE_COUNT = 0
            solver_trans = Solver(name='g3')
            T = Invariant(k_aut)
            trans_alphabet = restricted_transducer.get_all_symbols()

            # generate conditions for transducer
            # 1) determinism
            generate_condition_for_determinism(trans_alphabet, T, solver_trans)
            # 2) completeness
            #generate_condition_for_completeness(trans_alphabet, T, solver_trans)
            # 3) at least one accepting state
            generate_condition_for_accepting_states(trans_alphabet, T, solver_trans)
            # 4) symmetry breaking
            # TODO

            # solve
            solver_trans.solve()
            for model in solver_trans.enum_models():
                # convert to automaton instance
                T_aut = convert_model_to_automaton(
                    model = model,
                    used_alphabet = trans_alphabet,
                    inv = T, 
                    symbol_map = restricted_transducer.symbol_map.copy()
                )
                # check conditions
                # 1) strict preorder (irreflexivity & transitivity)
                if contains_eventually_operator:
                    # without F, all transitions are accepting
                    is_strict_preorder = invariant_conditions.is_strict_preorder(T_aut, A_aut)
                    if not is_strict_preorder:
                        continue
                # 2) trace quantifier condition
                transition_condition_holds = invariant_conditions.check_transition_invariant_condition(
                    extended_transducer = restricted_transducer,
                    accepting_trans = accepting_transitions,
                    invariant = A_aut,
                    relation = T_aut,
                    trace_quantifiers = trace_quantifiers,
                    system_transducer = original_transducer
                )
                if transition_condition_holds:
                    return A_aut, T_aut
                if not contains_eventually_operator:
                    # without F, no need to generate other transducers  
                    break
                
            solver_trans.delete()
        solver_aut.delete()

    # no advice bits were found for k_max
    return None, None 


def convert_model_to_automaton(
        model: list, 
        used_alphabet: list, 
        inv: Invariant,
        symbol_map: list
    ) -> automata.Automaton:
    # alphabet
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(automata.create_symbol_map(len(used_alphabet[0])))
    mata_nfa.store()["alphabet"] = alphabet
    
    # create automaton
    new_aut = mata_nfa.Nfa(inv.num_states)
    # initial state
    # states labeled from 0 -> variable-1
    new_aut.make_initial_state(0)
    # accepting states
    for state in inv.state_variables:
        if state in model:
            new_aut.make_final_state(state-1-len(inv.trans_variables))

    # transitions
    for src_index in range(inv.num_states):
        for symbol_index in range(len(used_alphabet)):
            for dst_index in range(inv.num_states):
                var_index = src_index * len(used_alphabet) * inv.num_states + symbol_index * inv.num_states + dst_index + 1
                symbol = used_alphabet[symbol_index]
                if var_index in model:
                    new_aut.add_transition(src_index, symbol, dst_index)
    new_aut.label = "Symbols: " + str(symbol_map.copy())
    
    result = automata.Automaton(
        automaton = new_aut,
        alphabet = alphabet,
        symbol_map = symbol_map.copy(),
        number_of_tapes = len(symbol_map),
        atomic_propositions = symbol_map[0]
    )
    result.automaton = automata.minimize(result)
    return result 

if __name__ == "__main__":
    # SAT solver test
    solver = Solver(name='g3')
    # example for (x1 & !x2) | x3 <=> (x1 | x3) & (!x2 | x3)
    solver.add_clause([1, 3])
    solver.add_clause([-2, 3])
    for model in solver.enum_models():
        print(model)