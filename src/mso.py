import libmata.nfa.nfa as mata_nfa
import libmata.alphabets as alphabets
import automata

class MSOFormula:
    def __init__(self):
        self.one_bit_mapping = {"0":0, "1":1}
        self.two_bit_mapping = {"00":0, "01":1, "10":2, "11":3}
    
    def process_in_process_set(self, process_var, process_set_var):
        config = mata_nfa.store()
        config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(self.two_bit_mapping)
        
        # construct mata automaton for i in I
        i_in_I = mata_nfa.Nfa(2, label=process_var + " in " + process_set_var)
        i_in_I.make_initial_state(0)
        i_in_I.add_transition(0, "00", 0)
        i_in_I.add_transition(0, "01", 0)
        i_in_I.add_transition(0, "11", 1)
        i_in_I.add_transition(1, "00", 1)
        i_in_I.add_transition(1, "01", 1)
        i_in_I.make_final_state(1)

        # maps indices to symbols
        symbol_map = [process_var, process_set_var]

        return automata.Automaton(i_in_I, config['alphabet'], symbol_map)
    
    def process_set_subseteq_process_set(self, process_set_var_1, process_set_var_2):
        config = mata_nfa.store()
        config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(self.two_bit_mapping)
        
        # construct mata automaton for I subseteq J
        I_subseteq_J = mata_nfa.Nfa(1, label=process_set_var_1 + " subseteq " + process_set_var_2)
        I_subseteq_J.make_initial_state(0)
        I_subseteq_J.add_transition(0, "00", 0)
        I_subseteq_J.add_transition(0, "01", 0)
        I_subseteq_J.add_transition(0, "11", 0)
        I_subseteq_J.make_final_state(0)

        # maps indices to symbols
        symbol_map = [process_set_var_1, process_set_var_2]

        return automata.Automaton(I_subseteq_J, config['alphabet'], symbol_map)
    
    def process_successor(self, predecessor, successor):
        config = mata_nfa.store()
        config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(self.two_bit_mapping)

        # construct mata automaton for j = succ(i)
        process_successor = mata_nfa.Nfa(3, label=successor + " = succ(" + predecessor + ")")
        process_successor.make_initial_state(0)
        process_successor.add_transition(0, "00", 0)
        process_successor.add_transition(0, "10", 1)
        process_successor.add_transition(1, "01", 2)
        process_successor.add_transition(2, "00", 2)
        process_successor.make_final_state(2)

        # maps indices to symbols
        symbol_map = [predecessor, successor]

        return automata.Automaton(process_successor, config['alphabet'], symbol_map)
    
    def singleton(self, aut: automata.Automaton, index: int):
        config = mata_nfa.store()
        config['alphabet'] = aut.alphabet

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

        return automata.Automaton(sing, config['alphabet'], aut.symbol_map)

    def atomic_proposition(self, symbol, trace_var, process_var):
        config = mata_nfa.store()
        config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(self.two_bit_mapping)

        # construct mata automaton for parameterized atomic proposition
        ap = mata_nfa.Nfa(2, label=symbol+"_"+trace_var+"["+process_var+"]")
        ap.make_initial_state(0)
        ap.make_final_state(1)
        ap.add_transition(0, "00", 0)
        ap.add_transition(0, "10", 0)
        ap.add_transition(0, "11", 1)
        ap.add_transition(1, "00", 1)
        ap.add_transition(1, "10", 1)

        # maps indices to symbols
        symbol_map = [symbol+"_"+trace_var, process_var]

        return automata.Automaton(ap, config['alphabet'], symbol_map)
    
    def configuration_variable(self, config_var):
        config = mata_nfa.store()

        # configuration variable without parameter
        if "[" not in config_var:
            config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(self.one_bit_mapping)
            aut = mata_nfa.Nfa(1, label=config_var)
            aut.make_initial_state(0)
            aut.make_final_state(1)
            aut.add_transition(0, "1", 0)

            symbol_map = [config_var]

        # parameterized configuration variable
        else:
            config['alphabet'] = alphabets.OnTheFlyAlphabet.from_symbol_map(self.two_bit_mapping)
            var_name = config_var[:len(config_var)-3]
            process_name = config_var[-2]
            aut = mata_nfa.Nfa(2, label=config_var)
            aut.make_initial_state(0)
            aut.make_final_state(1)
            aut.add_transition(0, "00", 0)
            aut.add_transition(0, "10", 0)
            aut.add_transition(0, "11", 1)
            aut.add_transition(1, "00", 1)
            aut.add_transition(1, "10", 1)

            # maps indices to symbols
            symbol_map = [var_name, process_name]

        return automata.Automaton(aut, config['alphabet'], symbol_map)