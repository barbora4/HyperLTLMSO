import parse
import lark
from enum import Enum
import automata
import mso
import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting

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
    
    def is_existential_quantifier(self):
        return self.data[0] in [TreeOperators.EXISTS.value, TreeOperators.EXISTS]
    
    def is_universal_quantifier(self):
        return self.data[0] in [TreeOperators.FORALL.value, TreeOperators.FORALL]   

def print_tree(root: Node, tabs = 0):
    print("\t" * tabs + str(root.data))
    if (root.left != None):
        print_tree(root.left, tabs+1)
    if (root.right != None):
        print_tree(root.right, tabs+1)

class Formula:
    def __init__(self, tree, atomic_propositions):
        self.original_formula = TreeConvertor()
        self.original_formula.visit(parse.Transformer().transform(tree))
        
        # list of trace quantifiers in prefix
        self.trace_quantifiers_list = self.original_formula.trace_quantifiers_list 

        self.bnf = BnfFormula()
        self.bnf.translate_formula_into_bnf(self.original_formula.root) 

        self.mso_converter = mso.MSOFormula(self.trace_quantifiers_list, atomic_propositions)
        self.mso_initial_automaton = None 
        self.mso_local_constraints_transducer = None

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

    def plot_mso_initial_automaton(self):
        self.mso_initial_automaton.plot_automaton()

    def plot_local_constraints_transducer(self):
        self.mso_local_constraints_transducer.plot_automaton()

    def make_initial_automaton(self):
        self.mso_initial_automaton = self.convert_formula_to_automaton(self.bnf.mso_formula)
        self.mso_initial_automaton.automaton = automata.minimize(self.mso_initial_automaton)

    def make_local_constraints_transducer(self):
        #TODO convert all constraints
        self.mso_local_constraints_transducer = self.convert_formula_to_automaton(self.bnf.local_constraints[0])
        self.mso_local_constraints_transducer.automaton = automata.minimize(self.mso_local_constraints_transducer)

    def convert_formula_to_automaton(self, formula: Node):
        # return mso automaton for atomic formulae
        automaton = None
        if formula.is_atomic_formula():
            # new configuration variable
            if isinstance(formula.data, str):
                automaton = self.mso_converter.configuration_variable(formula.data)
            # i in I
            elif len(formula.data) == 3 and formula.data[1] == TreeOperators.IN.value:
                automaton = self.mso_converter.process_in_process_set(formula.data[0], formula.data[2])
            # I subseteq J
            elif len(formula.data) == 3 and formula.data[1] == TreeOperators.SUBSETEQ.value:
                automaton = self.mso_converter.process_set_subseteq_process_set(formula.data[0], formula.data[2])
            # j = succ(i)
            elif len(formula.data) == 6 and formula.data[2] == TreeOperators.SUCC.value:
                automaton = self.mso_converter.process_successor(formula.data[4], formula.data[0])
            # atomic proposition
            elif len(formula.data) == 3:
                automaton = self.mso_converter.atomic_proposition(formula.data[0], formula.data[1], formula.data[2])

        elif formula.data == TreeOperators.AND:
            # convert both subtrees to an automaton
            aut1 = self.convert_formula_to_automaton(formula.left)
            aut2 = self.convert_formula_to_automaton(formula.right)
            automaton = self.convert_and(aut1, aut2)

        elif formula.data == TreeOperators.OR:
            # convert both subtrees to an automaton
            aut1 = self.convert_formula_to_automaton(formula.left)
            aut2 = self.convert_formula_to_automaton(formula.right)
            automaton = self.convert_or(aut1, aut2)

        elif formula.data == TreeOperators.NEG:
            child = self.convert_formula_to_automaton(formula.left)
            automaton = self.convert_negation(child)

        elif formula.data == TreeOperators.IMPLIES:
            left_child = self.convert_formula_to_automaton(formula.left)
            right_child = self.convert_formula_to_automaton(formula.right)
            automaton = self.convert_implication(left_child, right_child)

        elif formula.data == TreeOperators.IFF:
            left_child = self.convert_formula_to_automaton(formula.left)
            right_child = self.convert_formula_to_automaton(formula.right)
            automaton = self.convert_equivalence(left_child, right_child)

        elif formula.data == TreeOperators.NEXT:
            # transducer
            # configuration variable on the second tape (next step)
            child = formula.left
            if child.is_atomic_formula() and isinstance(child.data, str):
                automaton = self.mso_converter.configuration_variable(child.data, next_step=True)
            else:
                raise ValueError("Next is allowed only for configuration variables!")

        elif formula.is_existential_quantifier():
            child = self.convert_formula_to_automaton(formula.left)
            var_to_remove = formula.data[1]
            automaton = self.convert_existential_quantifier(child, var_to_remove)

        elif formula.is_universal_quantifier():
            # forall i. phi <=> ! exists i. ! phi
            child = self.convert_formula_to_automaton(formula.left)
            child_neg = self.convert_negation(child)
            var_to_remove = formula.data[1]
            exists_child_neg = self.convert_existential_quantifier(child_neg, var_to_remove)
            automaton = self.convert_negation(exists_child_neg)
        
        return automaton
    
    def convert_existential_quantifier(self, aut: automata.Automaton, var_to_remove: str):        
        # find variable to remove on the last tape 
        index_to_remove = aut.symbol_map[-1].index(var_to_remove)
        automaton = automata.remove_symbol_on_index(aut, index_to_remove)

        if aut.number_of_tapes - len(self.trace_quantifiers_list) == 2:
            # transducer -> remove variable on last two tapes
            index_to_remove = automaton.symbol_map[-2].index(var_to_remove)
            automaton = automata.remove_symbol_on_index(automaton, index_to_remove, second_to_last=True)

        return automaton
    
    def convert_equivalence(self, aut1: automata.Automaton, aut2:automata.Automaton):
        # A <-> B <=> (A -> B) & (B -> A)
        left_implication = self.convert_implication(aut1, aut2)
        right_implication = self.convert_implication(aut2, aut1)
        automaton = self.convert_and(left_implication, right_implication)
        return automaton
    
    def convert_implication(self, aut1: automata.Automaton, aut2: automata.Automaton):
        # A -> B <=> !A | B
        aut1_neg = self.convert_negation(aut1)
        automaton = self.convert_or(aut1_neg, aut2)
        return automaton 
    
    def force_singletons(self, automaton: automata.Automaton):
        # indices of configuration tapes
        configuration_tapes = [i+1 for i in range(automaton.number_of_tapes - len(self.trace_quantifiers_list))]
        for tape_index in configuration_tapes:
            prefix_length = sum(len(map) for map in automaton.symbol_map[:-tape_index])
            # first order variables must be singletons (only occuring on the last tape)
            for index, symbol in enumerate(automaton.symbol_map[-tape_index]):
                # first order variables without parameter
                if symbol.islower() and len(symbol)==1:
                    sing = self.mso_converter.singleton(automaton, prefix_length+index)
                    # intersection with result
                    automaton.automaton = automata.intersection(
                        automaton,
                        sing
                    )

    def force_same_process_vars(self, automaton: automata.Automaton):
        # process and process set variables must be the same in the next step
        if automaton.number_of_tapes - len(self.trace_quantifiers_list) != 2:
            # only for transducers
            return  
        
        # process vars are denoted by one symbol
        # find indices to check
        indices = list()
        for i, symbol in enumerate(automaton.symbol_map[-1]):
            if len(symbol) == 1:
                indices.append(i)

        mata_nfa.store()["alphabet"] = automaton.alphabet
        transitions_to_remove = list()
        alphabet_map = automaton.alphabet.get_symbol_map()
        first_tape_position = sum(len(map) for map in automaton.symbol_map[:-2])
        second_tape_position = sum(len(map) for map in automaton.symbol_map[:-1])
        for t in automaton.automaton.get_trans_as_sequence():
            current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
            for index in indices:
                if current_symbol[first_tape_position+index] != current_symbol[second_tape_position+index]:
                    transitions_to_remove.append(t)
                    break

        # remove transitions
        for t in transitions_to_remove:
            automaton.automaton.remove_trans(t)
    
    def convert_negation(self, aut: automata.Automaton):
        # automata complementation
        automaton = automata.Automaton(
            automata.complement(aut),
            aut.alphabet,
            aut.symbol_map.copy(),
            aut.number_of_tapes,
            aut.atomic_propositions
        )

        # first order variables must be singletons
        self.force_singletons(automaton)
        self.force_same_process_vars(automaton)

        automaton.automaton = automata.minimize(automaton)

        return automaton 
    
    def get_new_transducer_symbol_map(self, aut1: automata.Automaton, aut2: automata.Automaton):
        all_first_tape = list(set(aut1.symbol_map[-2]).union(set(aut2.symbol_map[-2])))
        all_second_tape = list(set(aut1.symbol_map[-1]).union(set(aut2.symbol_map[-1])))
        return list(set(all_first_tape).union(set(all_second_tape)))

    def convert_and(self, aut1: automata.Automaton, aut2: automata.Automaton):
        if aut1.number_of_tapes == aut2.number_of_tapes:
            # extend alphabet of last tapes (configuration and process variables)
            symbol_map_last_tape = list(set(aut1.symbol_map[-1]).union(set(aut2.symbol_map[-1])))
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape)
            new_symbol_map = aut1.symbol_map.copy()
            new_symbol_map[-1] = symbol_map_last_tape
            bigger_aut = aut1
            
        elif aut1.number_of_tapes > aut2.number_of_tapes:
            bigger_aut = aut1
            # create new configuration tape for a smaller automaton
            automata.create_new_tape(aut2)
            # all symbols on configuration tapes
            symbol_map_last_tape = self.get_new_transducer_symbol_map(aut1, aut2)
            # extend alphabets on both tapes
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape)
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape, second_to_last=True)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape, second_to_last=True)
            new_symbol_map = aut1.symbol_map.copy()

        elif aut2.number_of_tapes > aut1.number_of_tapes:
            bigger_aut = aut2
            # create new configuration tape for a smaller automaton
            automata.create_new_tape(aut1)
            # all symbols on configuration tapes
            symbol_map_last_tape = self.get_new_transducer_symbol_map(aut1, aut2)
            # extend alphabets on both tapes
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape.copy())
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape.copy(), second_to_last=True)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape.copy())
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape.copy(), second_to_last=True)
            new_symbol_map = aut1.symbol_map.copy()

        # automata intersection
        automaton = automata.Automaton(
            automata.intersection(aut1, aut2),
            bigger_aut.alphabet,
            new_symbol_map,
            bigger_aut.number_of_tapes,
            bigger_aut.atomic_propositions.copy() 
        )

        self.force_same_process_vars(automaton)
        automaton.automaton = automata.minimize(automaton)

        return automaton
    
    def convert_or(self, aut1: automata.Automaton, aut2: automata.Automaton):
        if aut1.number_of_tapes == aut2.number_of_tapes:
            # extend alphabet of last tapes (configuration and process variables)
            symbol_map_last_tape = list(set(aut1.symbol_map[-1]).union(set(aut2.symbol_map[-1])))
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape)
            new_symbol_map = aut1.symbol_map.copy()
            new_symbol_map[-1] = symbol_map_last_tape
            bigger_aut = aut1

        elif aut1.number_of_tapes > aut2.number_of_tapes:
            bigger_aut = aut1
            # create new configuration tape for a smaller automaton
            automata.create_new_tape(aut2)
            # all symbols on configuration tapes
            symbol_map_last_tape = self.get_new_transducer_symbol_map(aut1, aut2)
            # extend alphabets on both tapes
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape)
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape, second_to_last=True)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape, second_to_last=True)
            new_symbol_map = aut1.symbol_map.copy()

        elif aut2.number_of_tapes > aut1.number_of_tapes:
            bigger_aut = aut2
            # create new configuration tape for a smaller automaton
            automata.create_new_tape(aut1)
            # all symbols on configuration tapes
            symbol_map_last_tape = self.get_new_transducer_symbol_map(aut1, aut2)
            # extend alphabets on both tapes
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape)
            aut1 = automata.extend_alphabet_on_last_tape(aut1, symbol_map_last_tape, second_to_last=True)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape)
            aut2 = automata.extend_alphabet_on_last_tape(aut2, symbol_map_last_tape, second_to_last=True)
            new_symbol_map = aut1.symbol_map.copy()

        # automata union
        automaton = automata.Automaton(
            automata.union(aut1, aut2),
            bigger_aut.alphabet,
            new_symbol_map,
            bigger_aut.number_of_tapes,
            bigger_aut.atomic_propositions
        )
        
        # first order variables must be singletons
        self.force_singletons(automaton)
        self.force_same_process_vars(automaton)

        automaton.automaton = automata.minimize(automaton)

        return automaton
    

class TreeConvertor(lark.visitors.Interpreter):
    def __init__(self):
        self.root = None
        self.current = None
        self.trace_quantifiers_list = list()

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
        # add trace quantifier to a list
        self.trace_quantifiers_list.append(tree.children[0].children)
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

        elif node.type == NodeType.ATOMIC_PROPOSITION and node.parent != None:
            node.parent.free_fo_variables.add(node.data[2])

        elif node.type == NodeType.PROCESS_QUANTIFIER:
            # remove variable from the set of free variables
            try:
                node.free_fo_variables.remove(node.data[1])
            except:
                #TODO handle SO variables
                pass

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
                if free_variable != "":
                    root = Node(NodeType.PROCESS_QUANTIFIER, [TreeOperators.FORALL, free_variable, TreeOperators.DOT], 1)
                    root.create_left_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.IFF, 2)
                    tmp = root.left
                else:
                    root = Node(NodeType.BOOLEAN_OPERATOR, TreeOperators.IFF, 2)
                    tmp = root
                tmp.create_left_child(NodeType.CONFIGURATION_VARIABLE, new_variable, 0)
                tmp.create_right_child(NodeType.BOOLEAN_OPERATOR, TreeOperators.AND if node.data == TreeOperators.ALWAYS.value else TreeOperators.OR, 2)
                tmp.right.create_right_child(NodeType.LTL_OPERATOR, TreeOperators.NEXT, 1)
                tmp.right.right.create_left_child(NodeType.CONFIGURATION_VARIABLE, new_variable, 0)
                # place original subtree here
                tmp.right.left = node.left.copy()
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