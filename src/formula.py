import pprint
import parse
import lark
from enum import Enum

class NodeType(Enum):
    PROCESS_QUANTIFIER = 1
    LTL_OPERATOR = 2
    ATOMIC_PROPOSITION = 3
    BOOLEAN_OPERATOR = 4
    ATOMIC_FORMULA = 5

class Node:
    def __init__(self, type, data, capacity):
        self.type = type
        self.data = data
        self.capacity = capacity # max number of children
        self.children = 0 # actual number of children
        self.left = None
        self.right = None
        self.parent = None

    def copy(self):
        new_node = Node(self.type, self.data, self.capacity)
        new_node.children = self.children
        new_node.left = self.left
        new_node.right = self.right 
        new_node.parent = self.parent 
        return new_node

def print_tree(root, tabs = 0):
    print("\t" * tabs + str(root.data))
    if (root.left != None):
        print_tree(root.left, tabs+1)
    if (root.right != None):
        print_tree(root.right, tabs+1)

class Formula:
    def __init__(self, tree):
        self.original_formula = TreeConvertor()
        self.original_formula.visit(parse.Transformer().transform(tree))
        self.bnf = None 

    def print_original_formula(self):
        print_tree(self.original_formula.root)

class TreeConvertor(lark.visitors.Interpreter):
    def __init__(self):
        self.root = None
        self.current = None

    def create_node(self, type, data, capacity):
        new_node = Node(type, data, capacity)
        if self.root == None:
            self.root = new_node
        else:
            new_node.parent = self.current
            self.current.children += 1
            if self.current.left == None:
                self.current.left = new_node
            else:
                self.current.right = new_node
        self.current = new_node

    def go_back_to_unprocessed(self, node):
        tmp_node = node.copy()
        while tmp_node.parent != None and tmp_node.children == tmp_node.capacity:
            tmp_node = tmp_node.parent
        self.current = tmp_node 
    
    # convert formula to BNF without trace quantifiers
    def trace_quantifiers(self, tree):
        self.visit_children(tree)

    def process_quantifiers_head(self, tree):
        self.create_node(NodeType.PROCESS_QUANTIFIER, tree.children, 1)

    def ltl_formula(self, tree):
        self.visit_children(tree)

    def ltl_operator(self, tree):
        if len(tree.children) == 2:
            # F, G, X
            self.create_node(NodeType.LTL_OPERATOR, tree.children[0], 1)
            self.visit(tree.children[1])
        else:
            # weak until
            self.create_node(NodeType.LTL_OPERATOR, tree.children[1], 2)
            self.visit(tree.children[0])
            self.visit(tree.children[2])

    def parameterized_atomic_proposition(self, tree):
        # tree leaves
        self.create_node(NodeType.ATOMIC_PROPOSITION, tree.children, 0)
        # go back to first unprocessed node
        self.go_back_to_unprocessed(self.current)

    def boolean_operator(self, tree):
        if len(tree.children) == 2:
            self.create_node(NodeType.BOOLEAN_OPERATOR, tree.children[0], 1)
            self.visit(tree.children[1])
        else:
            # and, or
            self.create_node(NodeType.BOOLEAN_OPERATOR, tree.children[1], 2)
            self.visit(tree.children[0])
            self.visit(tree.children[2])

    def parentheses(self, tree):
        self.visit_children(tree)

    def atom(self, tree):
        # tree leaves
        self.create_node(NodeType.ATOMIC_FORMULA, tree.children, 0)
        # go back to first unprocessed node
        self.go_back_to_unprocessed(self.current)

    def __default__(self, tree):
        pass