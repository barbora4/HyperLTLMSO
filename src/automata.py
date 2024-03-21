import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting
import itertools
import re
import copy
import formula

class Automaton:
    def __init__(self, automaton: mata_nfa.Nfa, alphabet, symbol_map, number_of_tapes, atomic_propositions):
        self.automaton = automaton
        self.alphabet = alphabet
        self.symbol_map = symbol_map
        self.number_of_tapes = number_of_tapes
        self.atomic_propositions = atomic_propositions

    def plot_automaton(self):
        mata_nfa.store()["alphabet"] = self.alphabet
        plotting.plot(self.automaton)

class Transducer(Automaton):
    def __init__(self, automaton: mata_nfa.Nfa, alphabet, symbol_map, number_of_tapes, atomic_propositions):
        Automaton.__init__(self, automaton, alphabet, symbol_map, number_of_tapes, atomic_propositions)
        self.tapes_half = number_of_tapes / 2

def get_initial_configurations(inputFileName, symbol_map):
    # get FA from .mata
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(create_symbol_map(len(symbol_map)))
    mata_nfa.store()["alphabet"] = alphabet
    automaton = parser.from_mata(
        inputFileName, 
        alphabet
    )
    automaton.label = "Symbols: " + str(symbol_map)

    # symbols are in automaton.get_symbols()
    # they are mapped to numbers, symbol map is in alpha.get_symbol_map()
    return Automaton(automaton, alphabet, symbol_map, 1, symbol_map)

def union(aut1: Automaton, aut2: Automaton):
    mata_nfa.store()["alphabet"] = aut1.alphabet
    aut = mata_nfa.union(aut1.automaton, aut2.automaton)
    create_label(aut, aut1.symbol_map)
    return aut

def intersection(aut1: Automaton, aut2: Automaton):
    mata_nfa.store()["alphabet"] = aut1.alphabet
    aut = mata_nfa.intersection(aut1.automaton, aut2.automaton)
    create_label(aut, aut1.symbol_map)
    return aut

def complement(aut: Automaton):
    mata_nfa.store()["alphabet"] = aut.alphabet
    result = mata_nfa.complement(aut.automaton, aut.alphabet)
    create_label(result, aut.symbol_map)
    return result

def minimize(aut: Automaton):
    mata_nfa.store()["alphabet"] = aut.alphabet
    result = mata_nfa.minimize(aut.automaton)
    create_label(result, aut.symbol_map)
    return result

def determinize(aut: Automaton):
    mata_nfa.store()["alphabet"] = aut.alphabet
    result = mata_nfa.determinize(aut.automaton)
    create_label(result, aut.symbol_map)
    return result

def extend_alphabet_on_last_tape(aut: Automaton, new_symbol_map, second_to_last=False) -> Automaton:
    tape_index = -1 if not second_to_last else -2
    
    # add new variables
    # indices of new variables
    mapping = list()
    new_variables_count = 0
    for symbol in new_symbol_map:
        try:
            # find element in current alphabet on the last tape
            index = aut.symbol_map[tape_index].index(symbol)
            mapping.append(index)
        except:
            # symbol not present in the current alphabet
            mapping.append(None)
            new_variables_count += 1

    # generate all options for new variables
    new_variables = list(itertools.product([0,1], repeat=new_variables_count))

    # create new automaton
    number_of_symbols = 0
    for i, map in enumerate(aut.symbol_map):
        if second_to_last and i == len(aut.symbol_map)-2:
            number_of_symbols += len(new_symbol_map)
        elif (not second_to_last) and i == len(aut.symbol_map)-1:
            number_of_symbols += len(new_symbol_map)
        else:
            number_of_symbols += len(map)

    new_alphabet = create_symbol_map(number_of_symbols)
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet
    new_aut = mata_nfa.Nfa(aut.automaton.num_of_states())
    new_aut.make_initial_states(aut.automaton.initial_states)
    new_aut.make_final_states(aut.automaton.final_states)

    # change transitions
    alphabet_map = aut.alphabet.get_symbol_map()
    transitions = aut.automaton.get_trans_as_sequence()
    if not second_to_last:
        # change on the last tape
        prefix_length = sum(len(map) for map in aut.symbol_map[:-1])
        suffix_length = 0
    else:
        prefix_length = sum(len(map) for map in aut.symbol_map[:-2])
        suffix_length = len(aut.symbol_map[-1])
    for t in transitions:
        # t.source, t.symbol, t.target
        for option in new_variables:
            current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
            new_symbol = current_symbol[:prefix_length]
            new_variable_index = 0
            for position in mapping:
                if position != None:
                    new_symbol += current_symbol[position + prefix_length]
                else:
                    # new variable
                    new_symbol += str(option[new_variable_index])
                    new_variable_index += 1
            for j in range(suffix_length):
                new_symbol += current_symbol[prefix_length + (len(mapping) - new_variable_index) + j]
            # add new transition
            new_aut.add_transition(t.source, new_symbol, t.target)

    aut.symbol_map[tape_index] = new_symbol_map.copy()
    new_aut.label = "Symbols: " + str(aut.symbol_map)

    # change automaton alphabet
    return Automaton(new_aut, alphabet, aut.symbol_map.copy(), aut.number_of_tapes, aut.atomic_propositions)

def create_new_tape(aut: Automaton):
    aut.number_of_tapes += 1
    aut.symbol_map.append(list()) # new configuration tape
    aut.label = "Symbols: " + str(aut.symbol_map)

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
    aut.label = "Symbols: " + str(symbol_map)

def remove_symbol_on_index(aut: Automaton, index: int, second_to_last=False):
    tape_index = -2 if second_to_last else -1

    # create new automaton
    new_alphabet = create_symbol_map(len(aut.atomic_propositions) * (aut.number_of_tapes-1) + len(aut.symbol_map[-1]) - 1)
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet
    new_aut = mata_nfa.Nfa(aut.automaton.num_of_states())
    new_aut.make_initial_states(aut.automaton.initial_states)
    new_aut.make_final_states(aut.automaton.final_states)

    # new symbol map
    new_symbol_map = aut.symbol_map
    new_symbol_map[tape_index] = aut.symbol_map[tape_index][:index] + aut.symbol_map[tape_index][index+1:] if len(aut.symbol_map[tape_index]) > index+1 else aut.symbol_map[tape_index][:index]

    # change transitions
    alphabet_map = aut.alphabet.get_symbol_map()
    transitions = aut.automaton.get_trans_as_sequence()
    if not second_to_last:
        # change on the last tape
        prefix_length = sum(len(map) for map in aut.symbol_map[:-1])
    else:
        prefix_length = sum(len(map) for map in aut.symbol_map[:-2])
    for t in transitions:
        current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
        # remove character on index
        new_symbol = current_symbol[:index+prefix_length] + current_symbol[index+1+prefix_length:] if len(current_symbol) > index+1+prefix_length else current_symbol[:index+prefix_length]
        new_aut.add_transition(t.source, new_symbol, t.target)

    # change automaton alphabet
    return Automaton(new_aut, alphabet, new_symbol_map, aut.number_of_tapes, aut.atomic_propositions)

def create_extended_aut_map(aut_map: list, formula_map: list):
    new_map = aut_map
    for symbol in formula_map:
        if symbol not in new_map and len(symbol)>3 and symbol[0] not in new_map:
            if len(symbol)>3:
                new_map.append(symbol[0])
            else:
                new_map.append(symbol)

    return new_map

def create_extended_formula_map(formula_map: list, aut_map: list):
    new_map = formula_map.copy()
    for symbol in aut_map:
        r = re.compile(symbol+"_.*")
        matches = list(filter(r.match, formula_map))
        if len(matches) == 0:
            new_map.append(symbol)

    return new_map

def create_multitape_automaton(aut: Automaton, number_of_tapes: int):
    # first determinize the original automaton
    aut.automaton = determinize(aut)

    # create new alphabet
    symbols_on_tapes = [len(aut.symbol_map) for i in range(number_of_tapes)]
    new_alphabet = create_symbol_map(len(symbols_on_tapes) * number_of_tapes)
    transitions = aut.automaton.get_trans_as_sequence()
    alphabet_map = aut.alphabet.get_symbol_map()
    new_variables_count = (number_of_tapes - 2) * len(aut.symbol_map)
    new_variables = list(itertools.product([0,1], repeat=new_variables_count))
    
    new_symbol_map = [copy.deepcopy(aut.symbol_map) for _ in range(number_of_tapes-1)]
    new_symbol_map.append(list()) # one empty tape for auxiliary variables
    
    # composition of number_of_tapes automata
    # corresponds to creating number_of_tapes automata with all possible options on other tapes
    # and then performing intersection of these automata
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet
    automata_to_intersect = list()
    for i in range(number_of_tapes-1):
        # create alphabet
        new_aut = mata_nfa.Nfa(aut.automaton.num_of_states())
        new_aut.make_initial_states(aut.automaton.initial_states)
        new_aut.make_final_states(aut.automaton.final_states)

        # same symbols on corresponding tape, all options on other ones
        for t in transitions:
            for option in new_variables:
                current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
                symbol_before = ""
                for j in range(i*len(aut.symbol_map)):
                    symbol_before += str(option[j])
                new_symbol = symbol_before + current_symbol
                if len(option) > (i+1)*len(aut.symbol_map)-1:
                    symbol_after = ""
                    for j in range(i*len(aut.symbol_map), len(option)):
                        symbol_after += str(option[j])
                    new_symbol += symbol_after
                new_aut.add_transition(t.source, new_symbol, t.target)
        new_aut.label = "Symbols: " + str(new_symbol_map)

        automata_to_intersect.append(Automaton(new_aut, alphabet, new_symbol_map, number_of_tapes, aut.atomic_propositions))

    # intersect automata in the list
    current_automaton = automata_to_intersect[0]
    for i in range(1, len(automata_to_intersect)):
        current_automaton = Automaton(
            intersection(current_automaton, automata_to_intersect[i]),
            current_automaton.alphabet,
            current_automaton.symbol_map,
            current_automaton.number_of_tapes,
            current_automaton.atomic_propositions
        )

    # minimize the result
    current_automaton.automaton = minimize(current_automaton)

    return current_automaton 

def restrict_automaton_with_formula(aut: Automaton, formula_aut: Automaton, trace_quantifiers: list):
    # 1) create multitape automaton for initial configurations
    aut = create_multitape_automaton(aut, len(trace_quantifiers)+1)

    # 2) intersect with automaton for initial mso formula   
    # extend last tape alphabet in initial automaton
    symbol_map_last_tape = formula_aut.symbol_map[-1]
    aut = extend_alphabet_on_last_tape(aut, symbol_map_last_tape)
    
    aut.automaton = minimize(aut)
    formula_aut.automaton = minimize(formula_aut)
    result = Automaton(
        intersection(aut, formula_aut),
        formula_aut.alphabet,
        formula_aut.symbol_map,
        formula_aut.number_of_tapes,
        aut.atomic_propositions
    )
    result.automaton = minimize(result)

    return result 

def parse_transducer_from_file(filename, symbol_map) -> Transducer:
    with open(filename) as f:
        input = f.read().splitlines()

    number_of_tapes = 2
    new_symbol_map = [copy.deepcopy(symbol_map) for _ in range(2)]

    # create new alphabet
    new_alphabet = create_symbol_map(len(symbol_map)*2)
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet

    states = []
    initial_states = []
    final_states = []
    transitions = []
    for line in input:
        # check first line
        if line.startswith("@NFA-explicit"):
            continue
        # get states
        elif line.startswith("%States-enum"):
            states = line.split()[1:]
        # get initial states
        elif line.startswith("%Initial"):
            initial_states = line.split()[1:]
        # get final states
        elif line.startswith("%Final"):
            final_states = line.split()[1:]
        # transitions
        else:
            transitions.append(line.split())

    # create automaton
    automaton = mata_nfa.Nfa(len(states), label="Symbols: " + str(new_symbol_map))
    for state in initial_states:
        automaton.make_initial_state(states.index(state))
    for state in final_states:
        automaton.make_final_state(states.index(state))
    for t in transitions:
        if len(t) != 3:
            raise SyntaxError("Wrong input format")
        src = states.index(t[0])
        dst = states.index(t[2])
        symbol = t[1][:int(len(t[1])/2)] + t[1][(int(len(t[1])/2))+1:]
        automaton.add_transition(src, symbol, dst)

    return Transducer(automaton, alphabet, new_symbol_map, number_of_tapes, symbol_map)

def create_multitape_transducer(aut: Automaton, number_of_tapes: int):
    #TODO
    pass

def restrict_transducer_with_formula(aut: Automaton, formula_aut: Automaton, trace_quantifiers: list):
    #TODO
    pass 