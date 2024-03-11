#!/usr/bin/python3

import parse
from formula import Formula
import automata
import mso
import libmata.nfa.nfa as mata_nfa
import libmata.alphabets as alphabets

if __name__ == "__main__":
    grammar_parser = parse.create_parser("grammar.txt")
    args = parse.parse_command_line_arguments()

    # parse formula into tree
    with open(args["formula"]) as f:
        input_formula = f.read()
    tree = grammar_parser.parse(input_formula)
    formula = Formula(tree)
    # print formula parsed into Buchi Normal Form
    formula.print_formula()

    # load initial configuration of a system (.mata)
    initial_configurations = automata.get_initial_configurations(args["initial_config"])

    # create automaton for initial mso formula
    formula.make_initial_automaton()
    formula.print_mso_initial_automaton()