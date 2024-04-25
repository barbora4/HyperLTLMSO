#!/usr/bin/python3

from pysat.solvers import Solver
import itertools
import automata
import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting
import invariant_conditions
from pysat.formula import *

GLOBAL_VARIABLE_COUNT = 0

class Invariant:
    def __init__(self, num_states):
        self.num_states = num_states
        self.trans_variables = list()
        self.state_variables = list()
        self.used_alphabet = list()
        self.auxiliary_variables = list()

def get_all_words_from_projected_word(word: list, conf_variables: int):
    all_words = list()

    new_variables = list(itertools.product([0,1], repeat=conf_variables * len(word)))

    for option in new_variables:
        new_word = word.copy()
        for i in range(len(word)):
            for k in range(conf_variables):
                new_word[i] += str(option[i*conf_variables + k])
        all_words.append(new_word)

    return all_words 

def generate_condition_for_determinism(
        inv: Invariant,
        solver: Solver
    ):
    global GLOBAL_VARIABLE_COUNT

    # TODO
    #if inv.num_states < 2:
    #    return 

    # create transition variables
    # src+symbol+dst ordered alphabetically
    inv.trans_variables = list(range(1+GLOBAL_VARIABLE_COUNT, 1+GLOBAL_VARIABLE_COUNT+inv.num_states*inv.num_states*len(inv.used_alphabet)))
    GLOBAL_VARIABLE_COUNT += len(inv.trans_variables)

    # k possible targets for each state and symbol
    # -> math.comb(k, 2) clauses for each state and symbol
    for index_src in inv.trans_variables.copy()[::inv.num_states*len(inv.used_alphabet)]: 
        # every new source state
        for index_symbol in range(len(inv.used_alphabet)):
            all_variables = [index_src + index_symbol + j for j in range(inv.num_states)]
            # generate all clauses
            all_options = list(itertools.product(all_variables, repeat=2))
            for option in all_options:
                if option[0] != option[1]:
                    solver.add_clause([-(option[0]), -(option[1])])


def generate_condition_for_completeness(
        inv: Invariant,
        solver: Solver
    ):
    global GLOBAL_VARIABLE_COUNT

    for index_src in inv.trans_variables.copy()[::inv.num_states*len(inv.used_alphabet)]: 
        # every new source state
        for index_symbol in range(len(inv.used_alphabet)):
            all_variables = [index_src + index_symbol + j for j in range(inv.num_states)]
            # generate all clauses
            solver.add_clause(all_variables)


def generate_condition_for_accepting_states(
        inv: Invariant,
        solver: Solver
    ):
    global GLOBAL_VARIABLE_COUNT

    inv.state_variables = list(range(1+GLOBAL_VARIABLE_COUNT, 1+GLOBAL_VARIABLE_COUNT+inv.num_states))
    GLOBAL_VARIABLE_COUNT += len(inv.state_variables)

    # at least one accepting state
    solver.add_clause(inv.state_variables)

def find_transitions(
        src_index: int, 
        symbol: str, 
        invariant: Invariant
    ) -> list:
    trans_variables = invariant.trans_variables 
    transitions = list()
    symbol_index = invariant.used_alphabet.index(symbol)
    
    for k in range(invariant.num_states):
        t = trans_variables[src_index*len(invariant.used_alphabet)*invariant.num_states + symbol_index*invariant.num_states + k]
        transitions.append(t)

    return transitions

def get_src_from_variable(
        invariant: Invariant,
        variable: int,
    ) -> int :
        # one src is for num_symbols * num_states transitions
        return int((variable-1) / (len(invariant.used_alphabet) * invariant.num_states))

def add_words_to_be_accepted(
        words: list,
        solver: Solver,
        invariant: Invariant
    ):
    # at least one os the word in words should be accepted 
    global GLOBAL_VARIABLE_COUNT
    
    all_dnf_clauses = list()
    for word in words: 
        dnf_clauses = [[] for _ in range(invariant.num_states**(len(word)))] # N^(l-1) clauses

        for index, symbol in enumerate(word):
            number_of_repetitions = invariant.num_states ** (len(word)-1-index)

            clause_index = 0
            while clause_index < len(dnf_clauses):
                if index == 0:
                    src_index = 0
                else:
                    src_index = get_src_from_variable(invariant, dnf_clauses[clause_index][-1])
                transitions = find_transitions(src_index, symbol, invariant)
                for t in transitions:
                    for _ in range(number_of_repetitions):
                        dnf_clauses[clause_index].append(t)
                        clause_index += 1
        # add accepting state
        clause_index = 0
        while clause_index < len(dnf_clauses):
            for state in invariant.state_variables:
                dnf_clauses[clause_index].append(state)
                clause_index += 1
        all_dnf_clauses += dnf_clauses 

    # Tseytin transformation into CNF
    # new name for each clause 
    for clause in dnf_clauses:
        GLOBAL_VARIABLE_COUNT += 1
        invariant.auxiliary_variables.append(GLOBAL_VARIABLE_COUNT)
        # add new clauses to SAT solver
        for var in clause:
            solver.add_clause([var, -GLOBAL_VARIABLE_COUNT])
    # add final clause to SAT solver
    solver.add_clause([aux_var for aux_var in invariant.auxiliary_variables])
    invariant.auxiliary_variables = list()

def add_word_to_be_rejected(
    word: str,
    solver: Solver,
    relation: automata.Automaton
):
    global GLOBAL_VARIABLE_COUNT

    cnf_clauses = [[] for _ in range(relation.num_states**(len(word)))] # N^(l-1) clauses

    if len(word) == 0:
        solver.add_clause([-relation.state_variables[0]])
        return 

    for index, symbol in enumerate(word):
        number_of_repetitions = relation.num_states ** (len(word)-1-index)
        clause_index = 0
        while clause_index < len(cnf_clauses):
            if index == 0:
                src_index = 0
            else:
                src_index = get_src_from_variable(relation, cnf_clauses[clause_index][-1])
            transitions = find_transitions(src_index, symbol, relation)
            for t in transitions:
                for _ in range(number_of_repetitions):
                    cnf_clauses[clause_index].append(-t)
                    clause_index += 1

    # add accepting state
    clause_index = 0
    while clause_index < len(cnf_clauses):
        for state in relation.state_variables:
            cnf_clauses[clause_index].append(-state)
            clause_index += 1

    # add cnf clauses to solver
    for clause in cnf_clauses: 
        solver.add_clause(clause)


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
        # only symbols used on first tape of the transducer are in the alphabet
        A.used_alphabet = restricted_transducer.get_all_symbols_from_first_tape()

        # generate conditions for invariant
        # 1) determinism
        generate_condition_for_determinism(A, solver_aut)
        # 3) at least one accepting state
        generate_condition_for_accepting_states(A, solver_aut)
        # 4) symmetry breaking
        # TODO

        # solve
        solver_aut.solve()
        for model in solver_aut.enum_models():

            # convert to automaton instance
            A_aut = convert_model_to_automaton(
                model = model, 
                inv = A, 
                symbol_map = restricted_initial_conf.symbol_map.copy()
            )
            
            # check conditions
            # 1) inclusion of initial configurations
            initial_condition_holds = invariant_conditions.check_initial_invariant_condition(
                extended_initial_aut = restricted_initial_conf,
                invariant = A_aut
            )
            if not initial_condition_holds[0]:
                word  = initial_condition_holds[1]
                # this PROJECTED word should be accepted
                total_symbols = sum([len(map) for map in restricted_initial_conf.symbol_map.copy()])
                conf_variables = total_symbols - len(word[0])
                words = get_all_words_from_projected_word(word, conf_variables)
                add_words_to_be_accepted(words, solver_aut, A)
                continue
            
            # 2) inductiveness
            is_inductive = invariant_conditions.check_invariant_inductiveness(
                invariant = A_aut,
                extended_transducer = restricted_transducer
            )
            if not is_inductive[0]:
                continue
            
            # conditions for the invariant hold -> generate transducer
            GLOBAL_VARIABLE_COUNT = 0
            solver_trans = Solver(name='g3')
            T = Invariant(k_aut)
            T.used_alphabet = restricted_transducer.get_all_symbols()

            # generate conditions for transducer
            # 1) determinism
            generate_condition_for_determinism(T, solver_trans)
            # 3) at least one accepting state
            generate_condition_for_accepting_states(T, solver_trans)
            # 4) symmetry breaking
            # TODO

            # solve
            solver_trans.solve()
            for model in solver_trans.enum_models():
                # convert to automaton instance
                T_aut = convert_model_to_automaton(
                    model = model,
                    inv = T, 
                    symbol_map = restricted_transducer.symbol_map.copy()
                )
                # check conditions
                # 1) strict preorder (irreflexivity & transitivity)
                is_irreflexive = invariant_conditions.is_irreflexive(T_aut)
                if not is_irreflexive[0]:
                    word = is_irreflexive[1]
                    # this word should be rejected 
                    add_word_to_be_rejected(word, solver_trans, T)
                    continue
                is_transitive = invariant_conditions.is_transitive(T_aut, A_aut)
                if not is_transitive[0]:
                    continue  
                # 1.5) check backwards reachability
                backwards_reachability_holds = invariant_conditions.check_invariant_backwards_reachability(
                    invariant = A_aut,
                    extended_initial_aut = restricted_initial_conf,
                    relation = T_aut,
                    extended_transducer = restricted_transducer
                )
                if not backwards_reachability_holds[0]:
                    continue
                # 2) trace quantifier condition
                transition_condition_holds = invariant_conditions.check_transition_invariant_condition(
                    extended_transducer = restricted_transducer,
                    accepting_trans = accepting_transitions,
                    invariant = A_aut,
                    relation = T_aut,
                    trace_quantifiers = trace_quantifiers,
                    system_transducer = original_transducer,
                    extended_initial = restricted_initial_conf,
                )
                if transition_condition_holds:
                    return A_aut, T_aut
                
            solver_trans.delete()
        solver_aut.delete()

    # no advice bits were found for k_max
    return None, None 


def convert_model_to_automaton(
        model: list, 
        inv: Invariant,
        symbol_map: list
    ) -> automata.Automaton:
    # alphabet
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(automata.create_symbol_map(len(inv.used_alphabet[0])))
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
        for symbol_index in range(len(inv.used_alphabet)):
            for dst_index in range(inv.num_states):
                var_index = src_index * len(inv.used_alphabet) * inv.num_states + symbol_index * inv.num_states + dst_index + 1
                symbol = inv.used_alphabet[symbol_index]
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