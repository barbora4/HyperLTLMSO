#!/usr/bin/python3

import parse
from formula import Formula
import automata
import mso
import libmata 

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
    #formula.print_formula()

    # create automaton for initial mso formula
    formula.make_initial_automaton()
    #formula.plot_mso_initial_automaton()

    # extended initial configurations with MSO formula
    restricted_initial_conf = automata.restrict_automaton_with_formula(
        initial_configurations, 
        formula.mso_initial_automaton,
        formula.trace_quantifiers_list
    )
    #restricted_initial_conf.plot_automaton()

    # parse system transducer from file
    system_transducer = automata.parse_transducer_from_file(
        args["system_transducer"],
        symbol_map 
    )
    system_transducer.plot_automaton()