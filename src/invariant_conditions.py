import libmata.nfa.nfa as mata_nfa
from libmata import parser, alphabets, plotting
import automata
import itertools

def get_invariant_from_file(file_name: str, symbol_map: list) -> automata.Automaton:
    number_of_symbols = sum(len(map) for map in symbol_map)
    new_symbol_map = automata.create_symbol_map(number_of_symbols)
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

def get_relation_from_file(file_name: str, symbol_map: list) -> automata.Automaton:
    return automata.parse_transducer_from_file(
        file_name, 
        symbol_map, 
        with_configuration=True
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

def extend_automaton_to_transducer(
    aut: automata.Automaton, 
    tape_index: int
) -> automata.Automaton:
    new_variables_count = sum(len(map) for map in aut.symbol_map)
    new_variables = list(itertools.product([0,1], repeat=new_variables_count))

    new_alphabet = automata.create_symbol_map(2 * new_variables_count)
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet
    new_aut = mata_nfa.Nfa(aut.automaton.num_of_states())
    new_aut.make_initial_states(aut.automaton.initial_states)
    new_aut.make_final_states(aut.automaton.final_states)

    alphabet_map = aut.alphabet.get_symbol_map()
    transitions = aut.automaton.get_trans_as_sequence()
    for t in transitions:
        current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
        for option in new_variables:
            if tape_index == 0:
                new_symbol = current_symbol
                for j in range(len(option)):
                    new_symbol += str(option[j])
            elif tape_index == 1:
                new_symbol = ""
                for j in range(len(option)):
                    new_symbol += str(option[j])
                new_symbol += current_symbol
            else:
                raise ValueError("Tape index out of bounds")
            new_aut.add_transition(t.source, new_symbol, t.target)

    new_symbol_map = aut.symbol_map.copy() + aut.symbol_map.copy()
    new_aut.label = "Symbols: " + str(new_symbol_map)
    
    return automata.Automaton(
        new_aut,
        alphabet,
        new_symbol_map,
        aut.number_of_tapes * 2,
        aut.atomic_propositions
    )

def check_transition_invariant_condition(
    extended_transducer: automata.Automaton,
    accepting_trans: automata.Automaton,
    invariant: automata.Automaton,
    relation: automata.Automaton
) -> bool:
    # 1) both the current and the next configuration of the transducer
    # have to be in an invariant
    first = extend_automaton_to_transducer(invariant, 0)
    second = extend_automaton_to_transducer(invariant, 1)
    transducer_from_invariant = automata.Automaton(
        automata.intersection(first, second),
        first.alphabet,
        first.symbol_map.copy(),
        first.number_of_tapes,
        first.atomic_propositions
    )

    # they have to have symbol map in the same order
    # TODO

    # intersection
    extended_transducer_from_invariant = automata.Automaton(
        automata.intersection(transducer_from_invariant, extended_transducer),
        extended_transducer.alphabet,
        extended_transducer.symbol_map.copy(),
        extended_transducer.number_of_tapes,
        extended_transducer.atomic_propositions
    )
    extended_transducer_from_invariant.automaton = automata.minimize(extended_transducer_from_invariant)

    # 2) union of transducer for relation < and transducer for accepting transitions
    # they have to have symbol map in the same order
    # TODO

    # union
    relation_with_acc_trans = automata.Automaton(
        automata.union(relation, accepting_trans),
        accepting_trans.alphabet,
        accepting_trans.symbol_map.copy(),
        accepting_trans.number_of_tapes,
        accepting_trans.atomic_propositions
    )
    relation_with_acc_trans.automaton = automata.minimize(relation_with_acc_trans)

    # 3) intersection of extended relation with extended transducer
    transducer_with_relation = automata.Automaton(
        automata.intersection(
            extended_transducer_from_invariant,
            relation_with_acc_trans
        ),
        relation_with_acc_trans.alphabet,
        relation_with_acc_trans.symbol_map.copy(),
        relation_with_acc_trans.number_of_tapes,
        relation_with_acc_trans.atomic_propositions
    )
    transducer_with_relation.automaton = automata.minimize(transducer_with_relation)

    # 4) left side of the implication
    # on tapes with a universal quantifier, the original transition relation
    # of the system must hold
    # TODO

    # TODO
    pass