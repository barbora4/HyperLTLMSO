from lark import Lark, Transformer
import argparse

class TreeToJson(Transformer):
    # remove trace_quantifiers from tree
    def trace_quantifiers(self, s):
        if type(s) == list and len(s) == 1:
            return s[0]
        else:
            return s

    # remove ltl_formula from tree
    def ltl_formula(self, s):
        if type(s) == list and len(s) == 1:
            return s[0]
        else:
            return s
    
    # remove atom from tree
    def atom(self, s):
        if type(s) == list and len(s) == 1:
            return s[0]
        else: 
            return s
    
    # remove parameterized_atomic_proposition from tree
    def parameterized_atomic_proposition(self, s):
        if type(s) == list and len(s) == 1:
            return s[0]
        else:
            return s

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