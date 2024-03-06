#!/usr/bin/python3

import parse
from formula import Formula

if __name__ == "__main__":
    grammar_parser = parse.create_parser("grammar.txt")
    input_formula = parse.parse_command_line_arguments()

    # parse formula into tree
    tree = grammar_parser.parse(input_formula)
    formula = Formula(tree)
    formula.print_formula()