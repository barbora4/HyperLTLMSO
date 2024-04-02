#!/usr/bin/python3

import parse
from formula import Formula
import automata
import invariant_conditions

if __name__ == "__main__":
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
    #initial_configurations.plot_automaton()

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

    # generate and check conditions for the formula
    # invariant
    invariant = invariant_conditions.get_invariant_from_file(
        args["invariant"],
        restricted_initial_conf.symbol_map.copy()
    )

    # check if I subseteq projection(A)
    initial_condition_holds = invariant_conditions.check_initial_invariant_condition(
        restricted_initial_conf,
        invariant
    )
    if initial_condition_holds:
        print("Initial condition holds")
    else:
        print("Initial condition does not hold")