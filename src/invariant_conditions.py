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
):
    # 1) remove configuration tapes in both automata
    initial_projected = automata.remove_configuration_tape(extended_initial_aut)
    invariant_projected = automata.remove_configuration_tape(invariant)

    # 2) check if L(initial_projected) subseteq L(invariant_projected)
    is_subseteq = mata_nfa.is_included_with_cex(
        lhs = initial_projected.automaton,
        rhs = invariant_projected.automaton,
        alphabet = initial_projected.alphabet
    )

    # returns tuple (bool, counterexample_word)
    return is_subseteq 

def check_invariant_backwards_reachability(
    invariant: automata.Automaton,
    extended_initial_aut: automata.Automaton,
    relation: automata.Automaton,
    extended_transducer: automata.Automaton,
): 
    # cylindrification of extended initial configurations
    extended_initial_cylindrified = extend_automaton_to_transducer(
        aut = extended_initial_aut,
        tape_index = 1
    )

    # intersection of extened transducer and the relation
    trans_intersection = automata.Automaton(
        automata.intersection(extended_transducer, relation),
        relation.alphabet,
        relation.symbol_map.copy(),
        relation.number_of_tapes,
        relation.atomic_propositions
    )

    # union with extended transducer
    union_aut = automata.Automaton(
        automata.union(extended_initial_cylindrified, trans_intersection),
        trans_intersection.alphabet,
        trans_intersection.symbol_map.copy(),
        trans_intersection.number_of_tapes,
        trans_intersection.atomic_propositions
    )

    # cylindrified invariant to transducer
    first = extend_automaton_to_transducer(
        aut = invariant,
        tape_index = 0
    )
    second = extend_automaton_to_transducer(
        aut = invariant,
        tape_index =  1
    )
    cylindrified_invariant = automata.Automaton(
        automata.intersection(first, second),
        first.alphabet,
        first.symbol_map.copy(),
        first.number_of_tapes,
        first.atomic_propositions
    )

    # intersection with cylindrified invariant
    intersection_aut = automata.Automaton(
        automata.intersection(cylindrified_invariant, union_aut),
        union_aut.alphabet,
        union_aut.symbol_map.copy(),
        union_aut.number_of_tapes,
        union_aut.atomic_propositions
    )

    # remove first tape of intersection_aut
    aut_with_removed_tape = project_transducer_to_automaton(
        aut = intersection_aut,
        tape_index_to_remove = 0
    )

    is_subseteq = mata_nfa.is_included_with_cex(
        lhs = invariant.automaton,
        rhs = aut_with_removed_tape.automaton,
        alphabet = invariant.alphabet
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

def project_transducer_to_automaton(
    aut: automata.Automaton,
    tape_index_to_remove: int      
) -> automata.Automaton:
    variables_count = sum(len(map) for map in aut.symbol_map)

    new_alphabet = automata.create_symbol_map(int(variables_count/2))
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet
    new_aut = mata_nfa.Nfa(aut.automaton.num_of_states())
    new_aut.make_initial_states(aut.automaton.initial_states)
    new_aut.make_final_states(aut.automaton.final_states)

    alphabet_map = aut.alphabet.get_symbol_map()
    transitions = aut.automaton.get_trans_as_sequence()
    for t in transitions:
        current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
        if tape_index_to_remove == 0:
            new_aut.add_transition(t.source, current_symbol[int(variables_count/2):], t.target)
        elif tape_index_to_remove == 1:
            new_aut.add_transition(t.source, current_symbol[:int(variables_count/2)], t.target)
        else:
            raise ValueError("Wrong tape index")

    new_symbol_map = [aut.symbol_map[i].copy() for i in range(int(len(aut.symbol_map)/2))]
    new_aut.label = "Symbols: " + str(new_symbol_map)
    
    result =  automata.Automaton(
        new_aut, 
        alphabet,
        new_symbol_map,
        int(aut.number_of_tapes / 2),
        aut.atomic_propositions
    )
    result.automaton = automata.minimize(result)
    return result

def create_cylindrified_system_transducer(
    system_transducer: automata.Automaton,
    tape_index: int,
    extended_transducer: automata.Automaton
) -> automata.Automaton:
    # create new variables
    total_symbols = sum(len(map) for map in extended_transducer.symbol_map)
    symbols_in_system = sum(len(map) for map in system_transducer.symbol_map)
    new_variables_count = total_symbols - symbols_in_system
    new_variables = list(itertools.product([0,1], repeat=new_variables_count))

    # create new alphabet
    new_alphabet = automata.create_symbol_map(total_symbols)
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet

    # create new automaton
    new_aut = mata_nfa.Nfa(system_transducer.automaton.num_of_states())
    new_aut.make_initial_states(system_transducer.automaton.initial_states)
    new_aut.make_final_states(system_transducer.automaton.final_states)

    # change transitions
    alphabet_map = system_transducer.alphabet.get_symbol_map()
    transitions = system_transducer.automaton.get_trans_as_sequence()
    prefix_length = tape_index * len(system_transducer.atomic_propositions)
    length_between = int(total_symbols/2) - int(symbols_in_system/2)
    suffix_length = total_symbols - prefix_length - length_between - symbols_in_system
    for t in transitions:
        current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
        for option in new_variables:
            new_symbol = ""
            for j in range(prefix_length):
                new_symbol += str(option[j])
            new_symbol += current_symbol[:int(len(current_symbol)/2)]
            for j in range(length_between):
                new_symbol += str(option[j + prefix_length])
            new_symbol += current_symbol[int(len(current_symbol)/2):]
            for j in range(suffix_length):
                new_symbol += str(option[j + prefix_length + length_between])
            new_aut.add_transition(t.source, new_symbol, t.target)
    new_aut.label = "Symbols: " + str(extended_transducer.symbol_map)

    return automata.Automaton(
        automaton = new_aut,
        alphabet = alphabet,
        symbol_map = extended_transducer.symbol_map.copy(),
        number_of_tapes = extended_transducer.number_of_tapes,
        atomic_propositions = extended_transducer.atomic_propositions
    )

def remove_transducer_configuration_tapes(transducer: automata.Automaton) -> automata.Automaton:
    # new symbol map
    new_symbol_map = list()
    for i, map in enumerate(transducer.symbol_map):
        if i != int(transducer.number_of_tapes/2)-1 and i != int(transducer.number_of_tapes)-1:
            new_symbol_map.append(map)

    # new alphabet
    number_of_symbols = sum(len(map) for map in new_symbol_map)
    new_alphabet = automata.create_symbol_map(number_of_symbols)
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet

    # new automaton
    new_aut = mata_nfa.Nfa(transducer.automaton.num_of_states())
    new_aut.make_initial_states(transducer.automaton.initial_states)
    new_aut.make_final_states(transducer.automaton.final_states)

    # change transitions
    alphabet_map = transducer.alphabet.get_symbol_map()
    transitions = transducer.automaton.get_trans_as_sequence()
    conf_tape_length = int((sum(len(map) for map in transducer.symbol_map) - number_of_symbols)/2)
    first_tape_start = int(number_of_symbols/2)
    second_tape_start = number_of_symbols + conf_tape_length
    for t in transitions:
        current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
        new_symbol = current_symbol[:first_tape_start]
        new_symbol += current_symbol[first_tape_start+conf_tape_length:second_tape_start]
        new_symbol += current_symbol[second_tape_start+conf_tape_length:]
        new_aut.add_transition(t.source, new_symbol, t.target)
    new_aut.label = "Symbols: " + str(new_symbol_map)
    
    result = automata.Automaton(
        new_aut,
        alphabet,
        new_symbol_map,
        transducer.number_of_tapes - 2,
        transducer.atomic_propositions
    )
    result.automaton = automata.minimize(result)

    return result 

def process_all_trace_quantifiers(
    transducer: automata.Automaton,
    trace_quantifiers: list
) -> automata.Automaton:
    # start from the last quantifier
    for i, quantifier in enumerate(trace_quantifiers[::-1]):
        tape_index = len(trace_quantifiers) - 1 - i
        if quantifier[0] == "exists":
            transducer = process_existential_quantifier_on_last_tape(transducer)
        elif quantifier[0] == "forall":
            transducer = process_universal_quantifier_on_last_tape(transducer)
        else:
            raise ValueError("Not a valid quantifier")

    return transducer

def process_existential_quantifier_on_last_tape(
    transducer: automata.Automaton
) -> automata.Automaton:
    # remove last tape of the second step
    return automata.remove_configuration_tape(transducer)

def process_universal_quantifier_on_last_tape(
    transducer: automata.Automaton
) -> automata.Automaton:
    # forall y . phi <=> ! exists y. ! phi 
    # complement the transducer
    transducer_neg = automata.Automaton(
        automata.complement(transducer),
        transducer.alphabet,
        transducer.symbol_map.copy(),
        transducer.number_of_tapes,
        transducer.atomic_propositions
    )
    # remove y (last tape)
    tmp = process_existential_quantifier_on_last_tape(transducer_neg)
    # complement the result
    result = automata.Automaton(
        automata.complement(tmp),
        tmp.alphabet,
        tmp.symbol_map.copy(),
        tmp.number_of_tapes,
        tmp.atomic_propositions
    )
    result.automaton = automata.minimize(result)

    return result

def check_transition_invariant_condition(
    extended_transducer: automata.Automaton,
    accepting_trans: automata.Automaton,
    invariant: automata.Automaton,
    relation: automata.Automaton,
    trace_quantifiers: list,
    system_transducer: automata.Automaton,
    extended_initial: automata.Automaton
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
    
    # get indices of universal quantifiers
    universal_indices = [i for i in range(len(trace_quantifiers)) if trace_quantifiers[i][0] == "forall"]
    # create transducers where i-th tape corresponds to the transitions of the system
    # the content of the other tapes is arbitrary
    transducers_to_intersect = list()
    for index in universal_indices:
        new_transducer = create_cylindrified_system_transducer(
            system_transducer, 
            index,
            transducer_with_relation
        )
        transducers_to_intersect.append(new_transducer)
    # intersect the transducers
    if len(transducers_to_intersect) > 0:
        left_side_transducer = transducers_to_intersect[0]
        for i in range(1, len(transducers_to_intersect)):
            left_side_transducer = automata.Automaton(
                automata.intersection(left_side_transducer, transducers_to_intersect[i]),
                left_side_transducer.alphabet,
                left_side_transducer.symbol_map.copy(),
                left_side_transducer.number_of_tapes,
                left_side_transducer.atomic_propositions
            )
        # minimize the result
        left_side_transducer.automaton = automata.minimize(left_side_transducer)

        # 5) left_side_transducer => transducer_with_relation
        # union of the negation of left_side_transducer and transducer_with_relation
        left_side_transducer_neg = automata.Automaton(
            automata.complement(left_side_transducer),
            left_side_transducer.alphabet,
            left_side_transducer.symbol_map.copy(),
            left_side_transducer.number_of_tapes,
            left_side_transducer.atomic_propositions
        )
        whole_transducer_without_quantifiers = automata.Automaton(
            automata.union(left_side_transducer_neg, transducer_with_relation),
            left_side_transducer_neg.alphabet,
            left_side_transducer_neg.symbol_map.copy(),
            left_side_transducer_neg.number_of_tapes,
            left_side_transducer_neg.atomic_propositions
        )
    else:
        # no universal quantifiers -> right side of the implication always holds
        whole_transducer_without_quantifiers = transducer_with_relation

    # 6) quantifier projection
    # check if the result is not empty, if yes, return False
    if whole_transducer_without_quantifiers.automaton.is_lang_empty():
        return False
    
    # remove configuration tapes
    transducer = remove_transducer_configuration_tapes(whole_transducer_without_quantifiers)
    
    # process all trace quantifiers
    final_automaton = process_all_trace_quantifiers(transducer, trace_quantifiers)

    # 7) check if projection(A) subseteq final_automaton
    invariant_projected = automata.remove_configuration_tape(invariant)
    is_included = mata_nfa.is_included(
        lhs = invariant_projected.automaton,
        rhs = final_automaton.automaton,
        alphabet = final_automaton.alphabet
    )
    if is_included == True:
        return True
    else:
        return False 
    
def check_invariant_inductiveness(
        invariant: automata.Automaton,
        extended_transducer: automata.Automaton
    ):

    # transducer for x in A
    first = extend_automaton_to_transducer(invariant, 0)
    # transducer for y in A
    second = extend_automaton_to_transducer(invariant, 1)

    # intersection of extended_transducer and first
    intersection = automata.Automaton(
        automata.intersection(extended_transducer, first),
        extended_transducer.alphabet,
        extended_transducer.symbol_map.copy(),
        extended_transducer.number_of_tapes,
        extended_transducer.atomic_propositions
    ) 

    # language inclusion check
    is_included = mata_nfa.is_included_with_cex(
        lhs = intersection.automaton,
        rhs = second.automaton,
        alphabet = extended_transducer.alphabet
    )
    return is_included 
    
def get_transducer_post(
        automaton: automata.Automaton,
        transducer: automata.Automaton,
    ) -> automata.Automaton:
    
    # cylindify automaton to transducer
    cylindrified_automaton = extend_automaton_to_transducer(automaton, 0)

    # intersection with transducer
    intersection = automata.Automaton(
        automata.intersection(transducer, cylindrified_automaton),
        transducer.alphabet,
        transducer.symbol_map.copy(),
        transducer.number_of_tapes,
        transducer.atomic_propositions
    )

    # get automaton from the second tape of the transducer 
    post = remove_first_tape_of_transducer(intersection)

    return post

def remove_first_tape_of_transducer(transducer: automata.Automaton) -> automata.Automaton:
    # new symbol map
    new_symbol_map = [map for (i, map) in enumerate(transducer.symbol_map) if i < int(len(transducer.symbol_map)/2)]

    # new alphabet
    number_of_symbols = sum(len(map) for map in new_symbol_map)
    new_alphabet = automata.create_symbol_map(number_of_symbols)
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet

    # new automaton
    new_aut = mata_nfa.Nfa(transducer.automaton.num_of_states())
    new_aut.make_initial_states(transducer.automaton.initial_states)
    new_aut.make_final_states(transducer.automaton.final_states)

    # change transitions
    alphabet_map = transducer.alphabet.get_symbol_map()
    transitions = transducer.automaton.get_trans_as_sequence()
    for t in transitions:
        current_symbol = list(alphabet_map.keys())[list(alphabet_map.values()).index(t.symbol)]
        new_symbol = current_symbol[number_of_symbols:]
        new_aut.add_transition(t.source, new_symbol, t.target)
    new_aut.label = "Symbols: " + str(new_symbol_map)
    
    result = automata.Automaton(
        new_aut,
        alphabet,
        new_symbol_map,
        int(transducer.number_of_tapes / 2),
        transducer.atomic_propositions
    )
    result.automaton = automata.minimize(result)

    return result 

def is_strict_preorder(
        transducer: automata.Automaton,
        invariant: automata.Automaton
    ) -> bool:
    # irreflexivity
    irreflexive = is_irreflexive(transducer)
    if not irreflexive:
        return False

    # transitivity
    transitive = is_transitive(transducer, invariant)
    return transitive 

def is_irreflexive(transducer: automata.Automaton) -> bool:
    # identity
    identity = create_identity_transducer(transducer.symbol_map.copy())

    # intersection
    intersection = automata.Automaton(
        automata.intersection(transducer, identity),
        transducer.alphabet,
        transducer.symbol_map.copy(),
        transducer.number_of_tapes,
        transducer.atomic_propositions
    )

    # emptiness check
    is_empty = intersection.automaton.is_lang_empty()
    if is_empty == True:
        return True
    else:
        return False

def is_transitive(
        transducer: automata.Automaton,
        invariant: automata.Automaton
    ) -> bool:
    # get post(invariant)
    post_A = get_transducer_post(
        automaton = invariant,
        transducer = transducer
    )

    # get post(post(invariant))
    post_post_A = get_transducer_post(
        automaton = post_A,
        transducer = transducer
    )

    # check language inclusion
    is_included = mata_nfa.is_included(
        lhs = post_post_A.automaton,
        rhs = post_A.automaton,
        alphabet = invariant.alphabet
    )
    
    if is_included == True:
        return True
    else:
        return False 

def create_identity_transducer(symbol_map: list) -> automata.Automaton:
    # new symbol map
    new_symbol_map = symbol_map.copy() 

    # new alphabet
    number_of_symbols = sum(len(map) for map in new_symbol_map)
    new_alphabet = automata.create_symbol_map(number_of_symbols)
    alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
    mata_nfa.store()["alphabet"] = alphabet

    # new automaton
    new_aut = mata_nfa.Nfa(1)
    new_aut.make_initial_state(0)
    new_aut.make_final_state(0)

    # add transitions
    alphabet_map = alphabet.get_symbol_map()
    all_symbols = alphabet_map.keys()
    for symbol in all_symbols:
        if symbol[:int(len(symbol)/2)] == symbol[int(len(symbol)/2):]:
            new_aut.add_transition(0, symbol, 0)
    new_aut.label = "Symbols: " + str(new_symbol_map)
    
    result = automata.Automaton(
        new_aut,
        alphabet,
        new_symbol_map,
        len(symbol_map),
        symbol_map[0]
    )

    return result 