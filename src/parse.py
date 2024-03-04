from lark import Lark
import argparse

def create_parser(grammar_file_path):
    # HyperLTL(MSO) grammar
    with open(grammar_file_path) as f:
        grammar = f.read()
    return Lark(grammar, start="trace_quantifiers")

def parse_command_line_arguments():
    # parse command line arguments
    input_parser = argparse.ArgumentParser()
    input_parser.add_argument("--formula", help="path to the file with formula",
                              required=True)
    args = vars(input_parser.parse_args())

    # get input formula
    with open(args["formula"]) as f:
        formula = f.read()

    return formula