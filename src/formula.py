import pprint
import parse
import lark

class Formula:
    def __init__(self, tree):
        self.original_formula = parse.Transformer().transform(tree)
        self.bnf = None 

    def print_original_formula(self):
        pprint.pprint(self.original_formula)
        print()
        BNFConvertor().visit(self.original_formula)

class BNFConvertor(lark.visitors.Interpreter):
    # convert formula to BNF without trace quantifiers
    def trace_quantifiers(self, tree):
        # visit children from the last
        for i in reversed(range(len(tree.children))):
            self.visit(tree.children[i])

    def trace_quantifiers_head(self, tree):
        # skip trace quantifiers for now
        pass

    def ltl_formula(self, tree):
        for i in reversed(range(len(tree.children))):
            self.visit(tree.children[i])
    
    def process_quantifiers_head(self, tree):
        print("Process quantifiers: " + str(tree.children))

    def ltl_operator(self, tree):
        if (tree.children[0] == "F"):
            self.visit(tree.children[1])
        print("Temporal operator: " + str(tree.children))

    def parameterized_atomic_proposition(self, tree):
        print("Atomic proposition")

    def boolean_operator(self, tree):
        pass

    def __default__(self, tree):
        pass