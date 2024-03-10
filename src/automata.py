import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting

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

def plot_automaton(automaton):
    plotting.plot(automaton)

def union(aut1, aut2):
    return mata_nfa.union(aut1, aut2)