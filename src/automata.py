import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting
import itertools

class Automaton:
    def __init__(self, automaton: mata_nfa.Nfa, alphabet, symbol_map):
        self.automaton = automaton
        self.alphabet = alphabet
        self.symbol_map = symbol_map

    def plot_automaton(self):
        plotting.plot(self.automaton)

def get_initial_configurations(inputFileName, mappingFileName):
    # get symbol mapping
    with open(mappingFileName) as f:
        symbol_map = f.read().splitlines()
    
    # get FA from .mata
    config = mata_nfa.store()
    config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(create_symbol_map(len(symbol_map)))
    automaton = parser.from_mata(
        inputFileName, 
        config['alphabet']
    )
    automaton.label = "Symbols: " + str(symbol_map)

    # symbols are in automaton.get_symbols()
    # they are mapped to numbers, symbol map is in alpha.get_symbol_map()
    return Automaton(automaton, config['alphabet'], symbol_map)

def union(aut1: Automaton, aut2: Automaton):
    aut = mata_nfa.union(aut1.automaton, aut2.automaton)
    create_label(aut, aut1.symbol_map)
    return aut

def intersection(aut1: Automaton, aut2: Automaton):
    aut = mata_nfa.intersection(aut1.automaton, aut2.automaton)
    create_label(aut, aut1.symbol_map)
    return aut

def complement(aut: Automaton):
    result = mata_nfa.complement(aut.automaton, aut.alphabet)
    create_label(result, aut.symbol_map)
    return result

def minimize(aut: Automaton):
    result = mata_nfa.minimize(aut.automaton)
    create_label(result, aut.symbol_map)
    return result

def extend_alphabet(aut: Automaton, new_symbol_map) -> Automaton:
    # add new variables
    # indices of new variables
    mapping = list()
    new_variables_count = 0
    for symbol in new_symbol_map:
        try:
            # find element in current alphabet
            index = aut.symbol_map.index(symbol)
            mapping.append(index)
        except:
            # symbol not present in the current alphabet
            mapping.append(None)
            new_variables_count += 1

    # generate all options for new variables
    new_variables = list(itertools.product([0,1], repeat=new_variables_count))

    # create new automaton
    new_alphabet = create_symbol_map(len(new_symbol_map))
    config = mata_nfa.store()
    config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    new_aut = mata_nfa.Nfa(aut.automaton.num_of_states())
    new_aut.make_initial_states(aut.automaton.initial_states)
    new_aut.make_final_states(aut.automaton.final_states)

    # change transitions
    alphabet_map = aut.alphabet.get_symbol_map()
    transitions = aut.automaton.get_trans_as_sequence()
    for t in transitions:
        # t.source, t.symbol, t.target
        for option in new_variables:
            new_symbol = ""
            new_variable_index = 0
            for position in mapping:
                if position != None:
                    new_symbol += list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)][position]
                else:
                    # new variable
                    new_symbol += str(option[new_variable_index])
                    new_variable_index += 1
            # add new transition
            new_aut.add_transition(t.source, new_symbol, t.target)

    new_aut.label = "Symbols: " + str(new_symbol_map)

    # change automaton alphabet
    return Automaton(new_aut, config['alphabet'], new_symbol_map)

def create_symbol_map(length: int):
    if length <= 0:
        return []

    binary_numbers = []
    for i in range(2 ** length):
        binary_string = bin(i)[2:].zfill(length)
        binary_numbers.append(binary_string)

    result = dict()
    for index, item in enumerate(binary_numbers):
        result[item] = index

    return result

def create_label(aut: mata_nfa.Nfa, symbol_map):
    label = "Symbols: "
    for i, var in enumerate(symbol_map):
        label += var
        if i != len(symbol_map) - 1:
            label += ", "
    aut.label = label

def remove_symbol_on_index(aut: Automaton, index: int):
    # create new automaton
    new_alphabet = create_symbol_map(len(aut.symbol_map)-1)
    config = mata_nfa.store()
    config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    new_aut = mata_nfa.Nfa(aut.automaton.num_of_states())
    new_aut.make_initial_states(aut.automaton.initial_states)
    new_aut.make_final_states(aut.automaton.final_states)

    # new symbol map
    new_symbol_map = aut.symbol_map[:index] + aut.symbol_map[index+1:] if len(aut.symbol_map) > index+1 else aut.symbol_map[:index]

    # change transitions
    alphabet_map = aut.alphabet.get_symbol_map()
    transitions = aut.automaton.get_trans_as_sequence()
    for t in transitions:
        current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
        # remove character on index
        new_symbol = current_symbol[:index] + current_symbol[index+1:] if len(current_symbol) > index+1 else current_symbol[:index]
        new_aut.add_transition(t.source, new_symbol, t.target)

    # change automaton alphabet
    return Automaton(new_aut, config['alphabet'], new_symbol_map)

def restrict_automaton_with_formula(aut: Automaton, formula: Automaton, trace_quantifiers: list):
    # 1) extend alphabets of both automata
    new_symbol_map = list(set(aut.symbol_map).union(set(formula.symbol_map)))
    aut = extend_alphabet(aut, new_symbol_map)
    formula = extend_alphabet(formula, new_symbol_map)

    #TODO do not extend if t and t_t1 -> this is the same symbol but for tape number 1

    return aut