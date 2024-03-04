#!/usr/bin/python3

import parse

if __name__ == "__main__":
    grammar_parser = parse.create_parser("grammar.txt")
    formula = parse.parse_command_line_arguments()

    # parse formula into tree
    tree = grammar_parser.parse(formula)
    print(tree.pretty())
