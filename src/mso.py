import libmata.nfa.nfa as mata_nfa
import libmata.alphabets as alphabets
import automata
import itertools
import copy

class MSOFormula:
    def __init__(self, trace_quantifiers, atomic_propositions):
        self.trace_quantifiers = trace_quantifiers
        self.atomic_propositions = atomic_propositions
        self.one_bit_mapping = {"0":0, "1":1}
        self.two_bit_mapping = {"00":0, "01":1, "10":2, "11":3}
    
    def process_in_process_set(self, process_var, process_set_var):
        number_of_tapes = len(self.trace_quantifiers) + 1 # one extra tape for configuration an process variables
        symbol_map = [copy.deepcopy(self.atomic_propositions) for _ in range(len(self.trace_quantifiers))]
        # add process vars to the last tape
        symbol_map.append([process_var.value, process_set_var.value]) 
        
        # create new alphabet
        symbol_length = len(self.atomic_propositions) * len(self.trace_quantifiers) + 2
        new_alphabet = automata.create_symbol_map(symbol_length)
        alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
        mata_nfa.store()["alphabet"] = alphabet

        # generate all options for new variables
        new_variables_count = len(self.atomic_propositions) * len(self.trace_quantifiers)
        new_variables = list(itertools.product([0,1], repeat=new_variables_count))
        
        # construct mata automaton for i in I
        i_in_I = mata_nfa.Nfa(2, label="Symbols: " + str(symbol_map))
        i_in_I.make_initial_state(0)
        i_in_I.make_final_state(1)

        for option in new_variables:
            prefix = ""
            for i in range(new_variables_count):
                prefix += str(option[i])
        
            i_in_I.add_transition(0, prefix + "00", 0)
            i_in_I.add_transition(0, prefix + "01", 0)
            i_in_I.add_transition(0, prefix + "11", 1)
            i_in_I.add_transition(1, prefix + "00", 1)
            i_in_I.add_transition(1, prefix + "01", 1)

        return automata.Automaton(i_in_I, alphabet, symbol_map, number_of_tapes, self.atomic_propositions)
    
    def process_set_subseteq_process_set(self, process_set_var_1, process_set_var_2):
        number_of_tapes = len(self.trace_quantifiers) + 1 # one extra tape for configuration an process variables
        symbol_map = [copy.deepcopy(self.atomic_propositions) for _ in range(len(self.trace_quantifiers))]
        # add process vars to the last tape
        symbol_map.append([process_set_var_1.value, process_set_var_2.value]) 
        
        # create new alphabet
        symbol_length = len(self.atomic_propositions) * len(self.trace_quantifiers) + 2
        new_alphabet = automata.create_symbol_map(symbol_length)
        alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
        mata_nfa.store()["alphabet"] = alphabet

        # generate all options for new variables
        new_variables_count = len(self.atomic_propositions) * len(self.trace_quantifiers)
        new_variables = list(itertools.product([0,1], repeat=new_variables_count))
        
        # construct mata automaton for I subseteq J
        I_subseteq_J = mata_nfa.Nfa(1, label="Symbols: " + str(symbol_map))
        I_subseteq_J.make_initial_state(0)
        I_subseteq_J.make_final_state(0)

        for option in new_variables:
            prefix = ""
            for i in range(new_variables_count):
                prefix += str(option[i])
        
            I_subseteq_J.add_transition(0, prefix + "00", 0)
            I_subseteq_J.add_transition(0, prefix + "01", 0)
            I_subseteq_J.add_transition(0, prefix + "11", 0)

        return automata.Automaton(I_subseteq_J, alphabet, symbol_map, number_of_tapes, self.atomic_propositions)
    
    def process_successor(self, predecessor, successor):
        number_of_tapes = len(self.trace_quantifiers) + 1 # one extra tape for configuration an process variables
        symbol_map = [copy.deepcopy(self.atomic_propositions) for _ in range(len(self.trace_quantifiers))]
        # add process var to the last tape
        symbol_map.append([predecessor.value, successor.value]) 
        
        # create new alphabet
        symbol_length = len(self.atomic_propositions) * len(self.trace_quantifiers) + 2
        new_alphabet = automata.create_symbol_map(symbol_length)
        alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
        mata_nfa.store()["alphabet"] = alphabet

        # generate all options for new variables
        new_variables_count = len(self.atomic_propositions) * len(self.trace_quantifiers)
        new_variables = list(itertools.product([0,1], repeat=new_variables_count))

        # construct mata automaton for j = succ(i)
        process_successor = mata_nfa.Nfa(3, label="Symbols: " + str(symbol_map))
        process_successor.make_initial_state(0)
        process_successor.make_final_state(2)

        for option in new_variables:
            prefix = ""
            for i in range(new_variables_count):
                prefix += str(option[i])
            
            process_successor.add_transition(0, prefix + "00", 0)
            process_successor.add_transition(0, prefix + "10", 1)
            process_successor.add_transition(1, prefix + "01", 2)
            process_successor.add_transition(2, prefix + "00", 2)

        return automata.Automaton(process_successor, alphabet, symbol_map, number_of_tapes, self.atomic_propositions)
    
    def singleton(self, aut: automata.Automaton, index: int):
        # construct mata automaton for first-order variable on some index
        sing = mata_nfa.Nfa(2)
        sing.make_initial_state(0)
        sing.make_final_state(1)

        for symbol in list(aut.alphabet.get_symbol_map().keys()):
            if symbol[index] == "0":
                sing.add_transition(0, symbol, 0)
                sing.add_transition(1, symbol, 1)
            else:
                sing.add_transition(0, symbol, 1)
        
        return automata.Automaton(sing, aut.alphabet, aut.symbol_map, aut.number_of_tapes, aut.atomic_propositions)

    def atomic_proposition(self, symbol, trace_var, process_var):
        number_of_tapes = len(self.trace_quantifiers) + 1 # one extra tape for configuration an process variables
        for index, quantifier in enumerate(self.trace_quantifiers):
            if trace_var in quantifier:
                trace_index = index
                break
        symbol_map = [copy.deepcopy(self.atomic_propositions) for _ in range(len(self.trace_quantifiers))]
        # add process var to the last tape
        symbol_map.append(list(process_var.value)) 
        
        # create new alphabet
        symbol_length = len(self.atomic_propositions) * len(self.trace_quantifiers) + 1
        new_alphabet = automata.create_symbol_map(symbol_length)
        alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
        mata_nfa.store()["alphabet"] = alphabet

        # generate all options for new variables
        new_variables_count = len(self.atomic_propositions) * len(self.trace_quantifiers) - 1
        new_variables = list(itertools.product([0,1], repeat=new_variables_count))

        # construct mata automaton for parameterized atomic proposition
        ap = mata_nfa.Nfa(2, label="Symbols: " + str(symbol_map))
        ap.make_initial_state(0)
        ap.make_final_state(1)
        
        # trace var is in (trace_index) * len(self.atomic_propositions) + self.atomic_propositions.index(symbol)
        # process_var is in (trace_index+1) * len(self.atomic_propositions)
        ap_position = trace_index * len(self.atomic_propositions) + self.atomic_propositions.index(symbol)
        process_var_position = len(self.trace_quantifiers) * len(self.atomic_propositions)
        for option in new_variables:
            prefix = ""
            for i in range(ap_position):
                prefix += str(option[i])
            between = ""
            for i in range(ap_position+1, process_var_position):
                between += str(option[i-1])
            suffix = ""
            for i in range(process_var_position+1, len(option)):
                suffix += str(option[i-2])

            ap.add_transition(0, prefix + "0" + between + "0" + suffix, 0)
            ap.add_transition(0, prefix + "1" + between + "0" + suffix, 0)
            ap.add_transition(0, prefix + "1" + between + "1" + suffix, 1)
            ap.add_transition(1, prefix + "0" + between + "0" + suffix, 1)
            ap.add_transition(1, prefix + "1" + between + "0" + suffix, 1)
        
        return automata.Automaton(ap, alphabet, symbol_map, number_of_tapes, self.atomic_propositions)
    
    def configuration_variable(self, config_var, next_step=False):
        number_of_tapes = len(self.trace_quantifiers) + 1 # one extra tape for configuration variables
        symbol_map = [copy.deepcopy(self.atomic_propositions) for _ in range(len(self.trace_quantifiers))]
        if "[" not in config_var:
            config_var_name = config_var
            process_var = ""
        else:
            config_var_name = config_var[:len(config_var)-3]
            process_var = config_var[-2]
        symbol_map.append([config_var_name]) # one extra tape for configuration variables
        if process_var != "":
            symbol_map[-1].append(process_var) # add process variable

        # next step in transducer 
        if next_step:
            number_of_tapes += 1 # one more configuration tape for transducers
            symbol_map.append([config_var_name])
            if process_var != "":
                symbol_map[-1].append(process_var)
        
        # create new alphabet
        symbol_length = len(self.atomic_propositions) * len(self.trace_quantifiers) + 1
        if process_var != "":
            symbol_length += 1
        if next_step:
            symbol_length += 1
            if process_var != "":
                symbol_length += 1
        new_alphabet = automata.create_symbol_map(symbol_length)
        alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
        mata_nfa.store()["alphabet"] = alphabet

        # generate all options for new variables
        new_variables_count = len(self.atomic_propositions) * len(self.trace_quantifiers)
        if next_step:
            new_variables_count += 1
        new_variables = list(itertools.product([0,1], repeat=new_variables_count))

        # configuration variable without parameter
        if "[" not in config_var:
            aut = mata_nfa.Nfa(1, label="Symbols: " + str(symbol_map))
            aut.make_initial_state(0)
            aut.make_final_state(0)

            if next_step: 
                config_var_pos = len(self.atomic_propositions) * (number_of_tapes - 2)
            else:
                config_var_pos = len(self.atomic_propositions) * (number_of_tapes - 1) + len(symbol_map[-1]) - 1
            for option in new_variables:
                prefix = ""
                for i in range(len(option)):
                    prefix += str(option[i])
                aut.add_transition(0, prefix + "1", 0)

        # parameterized configuration variable
        else:
            aut = mata_nfa.Nfa(2, label="Symbols: " + str(symbol_map))
            aut.make_initial_state(0)
            aut.make_final_state(1)

            if next_step:
                config_var_pos = len(self.atomic_propositions) * (number_of_tapes - 2) + 1
            else:
                config_var_pos = len(self.atomic_propositions) * (number_of_tapes - 1) + len(symbol_map[-1]) - 2
            for option in new_variables:
                prefix = ""
                for i in range(config_var_pos):
                    prefix += str(option[i])
                # i stays the same for transducers
                prefix_i_zero = prefix + "0" if next_step else prefix
                prefix_i_one = prefix + "1" if next_step else prefix

                aut.add_transition(0, prefix_i_zero + "00", 0)
                aut.add_transition(0, prefix_i_zero + "10", 0)
                aut.add_transition(0, prefix_i_one + "11", 1)
                aut.add_transition(1, prefix_i_zero + "00", 1)
                aut.add_transition(1, prefix_i_zero + "10", 1)

        result = automata.Automaton(aut, alphabet, symbol_map, number_of_tapes, self.atomic_propositions)
        return result


    def configuration_variable_without_i(self, config_var):
        number_of_tapes = len(self.trace_quantifiers) + 1 # one extra tape for configuration variables
        symbol_map = [copy.deepcopy(self.atomic_propositions) for _ in range(len(self.trace_quantifiers))]
        if "[" not in config_var:
            config_var_name = config_var
            process_var = ""
        else:
            config_var_name = config_var[:len(config_var)-3]
            process_var = config_var[-2]
        symbol_map.append([config_var_name]) # one extra tape for configuration variables
        
        # create new alphabet
        symbol_length = len(self.atomic_propositions) * len(self.trace_quantifiers) + 1
        new_alphabet = automata.create_symbol_map(symbol_length)
        alphabet = alphabets.OnTheFlyAlphabet.from_symbol_map(new_alphabet)
        mata_nfa.store()["alphabet"] = alphabet

        # generate all options for new variables
        new_variables_count = len(self.atomic_propositions) * len(self.trace_quantifiers)
        new_variables = list(itertools.product([0,1], repeat=new_variables_count))

        aut = mata_nfa.Nfa(1, label="Symbols: " + str(symbol_map))
        aut.make_initial_state(0)
        aut.make_final_state(0)
        config_var_pos = len(self.atomic_propositions) * (number_of_tapes - 1) + len(symbol_map[-1]) - 1
        for option in new_variables:
            prefix = ""
            for i in range(config_var_pos):
                prefix += str(option[i])
            # i stays the same for transducers
            prefix_i_zero = prefix
            prefix_i_one = prefix
            aut.add_transition(0, prefix_i_zero + "1", 0)

        return automata.Automaton(aut, alphabet, symbol_map, number_of_tapes, self.atomic_propositions)