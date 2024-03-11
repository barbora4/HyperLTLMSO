import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting
import itertools

class Automaton:
    def __init__(self, automaton: mata_nfa.Nfa, alphabet, symbol_map):
        self.automaton = automaton
        self.alphabet = alphabet
        self.symbol_map = symbol_map

def get_initial_configurations(inputFileName):
    # get FA from .mata
    alpha = alphabets.OnTheFlyAlphabet()
    automaton = parser.from_mata(
        inputFileName, 
        alpha
    )

    # symbols are in automaton.get_symbols()
    # they are mapped to numbers, symbol map is in alpha.get_symbol_map()
    return automaton

def plot_automaton(automaton: Automaton):
    plotting.plot(automaton.automaton)

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

def extend_alphabet(aut: Automaton, new_symbol_map):
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