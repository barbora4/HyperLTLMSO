import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting
import automata

def get_invariant_from_file(file_name: str, symbol_map: list) -> automata.Automaton:
    new_symbol_map = automata.create_symbol_map(len(symbol_map))
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_symbol_map)
    mata_nfa.store()["alphabet"] = alphabet
    automaton = parser.from_mata(
        file_name,
        alphabet
    )
    automaton.label = "Symbols: " + str(symbol_map)

    return automata.Automaton(
        automaton, 
        alphabet, 
        symbol_map, 
        len(symbol_map), 
        symbol_map[0]
    )

def check_initial_invariant_condition(
        extended_initial_aut: automata.Automaton,
        invariant: automata.Automaton
    ) -> bool:
    # 1) remove configuration tapes in both automata
    initial_projected = automata.remove_configuration_tape(extended_initial_aut)
    invariant_projected = automata.remove_configuration_tape(invariant)

    # 2) check if L(initial_projected) subseteq L(invariant_projected)
    is_subseteq = mata_nfa.is_included(
        lhs = initial_projected.automaton,
        rhs = invariant_projected.automaton,
        alphabet = initial_projected.alphabet
    )

    return is_subseteq