import parse
import lark
from enum import Enum
import automata
import mso

class NodeType(Enum):
    PROCESS_QUANTIFIER = 1
    LTL_OPERATOR = 2
    ATOMIC_PROPOSITION = 3
    BOOLEAN_OPERATOR = 4
    ATOMIC_FORMULA = 5
    CONFIGURATION_VARIABLE = 6

class TreeOperators(Enum):
    IN = "in"
    SUBSETEQ = "subseteq"
    SUCC = "succ"
    EQUALS = "="
    FORALL = "forall"
    EXISTS = "exists"
    DOT = "."
    IFF = "<->"
    AND = "&"
    OR = "|"
    IMPLIES = "->"
    NEG = "!"
    EVENTUALLY = "F"
    ALWAYS = "G"
    NEXT = "X"
    WEAK_UNTIL = "W"

class Node:
    def __init__(self, type: NodeType, data, capacity: int):
        self.type = type
        self.data = data
        self.capacity = capacity # max number of children
        self.children = 0 # actual number of children

        self.left = None
        self.right = None
        self.parent = None

        self.processed = False
        self.free_fo_variables = set()

    def copy(self):
        new_node = Node(self.type, self.data, self.capacity)
        new_node.children = self.children
        new_node.left = self.left
        new_node.right = self.right 
        new_node.parent = self.parent 
        new_node.processed = self.processed 
        new_node.free_fo_variables = self.free_fo_variables
        return new_node
    
    def create_left_child(self, type: NodeType, data, capacity: int):
        new_node = Node(type, data, capacity)
        self.left = new_node
        self.children += 1
        new_node.parent = self

    def create_right_child(self, type: NodeType, data, capacity: int):
        new_node = Node(type, data, capacity)
        self.right = new_node
        self.children += 1
        new_node.parent = self

    def is_atomic_formula(self):
        return self.children == 0

def print_tree(root: Node, tabs = 0):
    print("\t" * tabs + str(root.data))
    if (root.left != None):
        print_tree(root.left, tabs+1)
    if (root.right != None):
        print_tree(root.right, tabs+1)

class Formula:
    def __init__(self, tree):
        self.original_formula = TreeConvertor()
        self.original_formula.visit(parse.Transformer().transform(tree))
        
        self.bnf = BnfFormula()
        self.bnf.translate_formula_into_bnf(self.original_formula.root) 

        self.mso_converter = mso.MSOFormula()
        self.mso_initial_automaton = None 

    def print_formula(self):
        print("MSO formula: ")
        print_tree(self.bnf.mso_formula)
        print("\n--------------------\n")
        print("Local constraints: ")
        for constraint in self.bnf.local_constraints:
            print_tree(constraint)
        print("\n--------------------\n")
        print("Eventuality constraints: ")
        for constraint in self.bnf.eventuality_constraints:
            print_tree(constraint)
        print("\n--------------------\n")

    def print_mso_initial_automaton(self):
        automata.plot_automaton(self.mso_initial_automaton)

    def make_initial_automaton(self):
        self.mso_initial_automaton = self.convert_formula_to_automaton(self.bnf.mso_formula)

    def convert_formula_to_automaton(self, formula: Node):
        #TODO automata operations
        #TODO symbol maps!

        # return mso automaton for atomic formulae
        automaton = None
        if formula.is_atomic_formula():
            # i in I
            if len(formula.data) == 3 and formula.data[1] == TreeOperators.IN.value:
                automaton = self.mso_converter.process_in_process_set(formula.data[0], formula.data[2])
            # I subseteq J
            elif len(formula.data) == 3 and formula.data[1] == TreeOperators.SUBSETEQ.value:
                automaton = self.mso_converter.process_set_subseteq_process_set(formula.data[0], formula.data[2])
            # j = succ(i)
            elif len(formula.data) == 6 and formula.data[2] == TreeOperators.SUCC.value:
                automaton = self.mso_converter.process_successor(formula.data[4], formula.data[0])

        elif formula.data in [TreeOperators.AND, TreeOperators.OR]:
            # convert both subtrees to an automaton
            aut1 = self.convert_formula_to_automaton(formula.left)
            aut2 = self.convert_formula_to_automaton(formula.right)

            # extend alphabet
            symbol_map = list(set(aut1.symbol_map).union(set(aut2.symbol_map)))
            aut1 = automata.extend_alphabet(aut1, symbol_map)
            aut2 = automata.extend_alphabet(aut2, symbol_map)

            if formula.data == TreeOperators.OR:
                # automata union
                automaton = automata.Automaton(
                    automata.union(aut1, aut2),
                    aut1.alphabet,
                    symbol_map
                )

                # first-order variables must be singletons
                for index, symbol in enumerate(symbol_map):
                    if symbol.islower():
                        sing = self.mso_converter.singleton(automaton, index)
                        # intersection with result
                        automaton.automaton = automata.intersection(
                            automaton,
                            sing
                        )
            elif formula.data == TreeOperators.AND:
                # automata intersection
                automaton = automata.Automaton(
                    automata.intersection(aut1, aut2),
                    aut1.alphabet,
                    symbol_map
                )

        return automaton

class TreeConvertor(lark.visitors.Interpreter):
    def __init__(self):
        self.root = None
        self.current = None

    def create_node(self, type: NodeType, data, capacity: int):
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

    def go_back_to_unprocessed(self, node: Node):
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
            # negation
            self.create_node(NodeType.BOOLEAN_OPERATOR, TreeOperators.NEG, 1)
            self.visit(tree.children[1])
        else:
            # and, or, implication, iff
            self.create_node(NodeType.BOOLEAN_OPERATOR, TreeOperators(tree.children[1]), 2)
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

class BnfFormula:
    def __init__(self):
        self.mso_formula = None
        self.local_constraints = list()
        self.eventuality_constraints = list()

        # the number of new configuration variables
        self.new_variables_count = 0
        self.new_variables_x = list()
        self.new_variables_y = list()

    def create_new_variable(self, fo_var = "", is_eventually = False):
        self.new_variables_count += 1
        suffix = str(self.new_variables_count)
        if fo_var != "":
            suffix += "[" + fo_var + "]"
        self.new_variables_x.append("x"+suffix)
        if is_eventually:
            self.new_variables_y.append("y"+suffix)
        return self.new_variables_x[-1]
    
    def translate_formula_into_bnf(self, original_formula):
        # original_formula is a root of the formula tree
        # post-order tree traversal
        self.mso_formula = original_formula
        self.translate_node(self.mso_formula)
    
    def translate_node(self, node):
        if node == None:
            return 
        
        # process children
        self.translate_node(node.left)
        self.translate_node(node.right)

        # process the current node
        if node.type == NodeType.ATOMIC_FORMULA:
            if node.data[1] == TreeOperators.IN.value:
                node.free_fo_variables.add(node.data[0])
            elif node.data[1] == TreeOperators.EQUALS.value:
                node.free_fo_variables.add(node.data[0])
                node.free_fo_variables.add(node.data[4])

        elif node.type == NodeType.ATOMIC_PROPOSITION:
            node.parent.free_fo_variables.add(node.data[2])

        elif node.type == NodeType.PROCESS_QUANTIFIER:
            # remove variable from the set of free variables
            node.free_fo_variables.remove(node.data[1])

        elif node.type == NodeType.LTL_OPERATOR:
            # find the name of at most one free fist-order variable
            # FO var in atom that is not quantified in this subtree
            free_variable = ""
            if len(node.free_fo_variables) == 1:
                free_variable = list(node.free_fo_variables)[0]
            elif len(node.free_fo_variables) > 1:
                raise ValueError("More than one free variable in LTL subformula")

            # create new configuration variable(s)
            new_variable = self.create_new_variable(free_variable, is_eventually=(node.data == TreeOperators.EVENTUALLY.value))

            # create local constraints
            if node.data in [TreeOperators.ALWAYS.value, TreeOperators.EVENTUALLY.value]: 
                root = Node(NodeType.PROCESS_QUANTIFIER, [TreeOperators.FORALL, free_variable, TreeOperators.DOT], 1)
                root.create_left_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.IFF, 2)
                root.left.create_left_child(NodeType.CONFIGURATION_VARIABLE, new_variable, 0)
                root.left.create_right_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.AND if node.data == TreeOperators.ALWAYS.value else TreeOperators.OR, 2)
                root.left.right.create_right_child(NodeType.LTL_OPERATOR, TreeOperators.NEXT, 1)
                root.left.right.right.create_left_child(NodeType.CONFIGURATION_VARIABLE, new_variable, 0)
                # place original subtree here
                root.left.right.left = node.left.copy()
                self.local_constraints.append(root)
            
            elif node.data == TreeOperators.WEAK_UNTIL.value:
                root = Node(NodeType.PROCESS_QUANTIFIER, [TreeOperators.WEAK_UNTIL, free_variable, TreeOperators.DOT], 1)
                root.create_left_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.IFF, 2)
                root.left.create_left_child(NodeType.CONFIGURATION_VARIABLE, new_variable, 0)
                root.left.create_right_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.DOT, 2)
                root.left.right.left = node.right.copy()
                root.left.right.create_right_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.AND, 2)
                root.left.right.right.left = node.left.copy()
                root.left.right.right.create_right_child(NodeType.LTL_OPERATOR, TreeOperators.NEXT, 1)
                root.left.right.right.right.create_left_child(NodeType.CONFIGURATION_VARIABLE, new_variable, 0)

            # eventuality variables
            if node.data ==  TreeOperators.EVENTUALLY.value:
                y_variable = new_variable.replace("x", "y")

                # create local constraints for eventuality variables
                root = Node(NodeType.PROCESS_QUANTIFIER, [TreeOperators.FORALL, free_variable, TreeOperators.DOT], 1)
                root.create_left_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.IMPLIES, 2)
                root.left.create_left_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.AND, 2)
                root.left.left.create_left_child(NodeType.CONFIGURATION_VARIABLE, y_variable, 0)
                root.left.left.create_right_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.NEG, 1)
                root.left.left.right.create_left_child(NodeType.LTL_OPERATOR, TreeOperators.NEXT, 1)
                root.left.left.right.left.create_left_child(NodeType.CONFIGURATION_VARIABLE, y_variable, 0)
                # place original subtree here
                root.left.right = node.left.copy()
                self.local_constraints.append(root)

                # create eventuality constraints
                root = Node(NodeType.PROCESS_QUANTIFIER, [TreeOperators.FORALL, free_variable, TreeOperators.DOT], 1)
                root.create_left_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.AND, 2)
                root.left.create_left_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.NEG, 1)
                root.left.left.create_left_child(NodeType.CONFIGURATION_VARIABLE, y_variable, 0)
                root.left.create_right_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.IMPLIES, 2)
                root.left.right.create_left_child(NodeType.LTL_OPERATOR, TreeOperators.NEXT, 1)
                root.left.right.left.create_left_child(NodeType.CONFIGURATION_VARIABLE, y_variable, 0)
                root.left.right.create_right_child(NodeType.LTL_OPERATOR, TreeOperators.NEXT, 1)
                root.left.right.right.create_left_child(NodeType.CONFIGURATION_VARIABLE, new_variable, 0)
                self.eventuality_constraints.append(root)
                
            # replace this subtree with new configuration variable
            node.data = new_variable
            node.left = None
            node.right = None
            node.capacity = 0
            node.children = 0
            node.processed = True 

        # give free fo variables to parent
        if node.parent != None:
            node.parent.free_fo_variables.update(node.free_fo_variables)