#!/usr/bin/python3

import parse
from formula import Formula
import automata
import invariant_conditions
import sat_solver
import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting
import time 

if __name__ == "__main__":
    start = time.time()
    
    MAX_NUM_STATES = 2
    
    grammar_parser = parse.create_parser("grammar.txt")
    args = parse.parse_command_line_arguments()

    # get symbol mapping
    with open(args["symbol_mapping"]) as f:
        symbol_map = f.read().splitlines()

    # load initial configuration of a system (.mata)
    initial_configurations = automata.get_initial_configurations(
        args["initial_config"],
        symbol_map
    )
    atomic_propositions = initial_configurations.atomic_propositions

    # parse formula into tree
    with open(args["formula"]) as f:
        input_formula = f.read()
    tree = grammar_parser.parse(input_formula)
    formula = Formula(tree, atomic_propositions)
    # print formula parsed into Buchi Normal Form
    formula.print_formula()

    # create automaton for initial mso formula
    formula.make_initial_automaton()

    # extended initial configurations with MSO formula
    restricted_initial_conf = automata.restrict_automaton_with_formula(
        initial_configurations, 
        formula.mso_initial_automaton,
        formula.trace_quantifiers_list
    )

    # parse system transducer from file
    system_transducer = automata.parse_transducer_from_file(
        args["system_transducer"],
        symbol_map 
    )

    # create transducer for local constraints of mso formula
    formula.make_local_constraints_transducer()

    # extended transducer for the system
    restricted_transducer = automata.restrict_transducer_with_formula(
       system_transducer,
       formula.mso_local_constraints_transducer,
       formula.trace_quantifiers_list
   )

    # transducer for eventuality constraints
    formula.make_eventuality_constraints_transducer()

    # conditions for SAT solver
    # get only used symbols (not the whole alphabet)
    used_alphabet = restricted_transducer.get_used_symbols()
    A, T = sat_solver.find_solution(
        max_k = MAX_NUM_STATES, # TODO input parameter
        restricted_initial_conf = restricted_initial_conf,
        restricted_transducer = restricted_transducer,
        original_transducer = system_transducer,
        accepting_transitions = formula.mso_eventuality_constraints_transducer,
        trace_quantifiers = formula.trace_quantifiers_list
    ) 

    if (A,T) == (None, None):
        print("Solution was not found for", MAX_NUM_STATES)
    else:
        end = time.time()
        print("Solution was found in", end-start, "seconds")
        # save the advice bits
        A.automaton.to_dot_file(output_file="A.dot", output_format="pdf")
        T.automaton.to_dot_file(output_file="T.dot", output_format="pdf")