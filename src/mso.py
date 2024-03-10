import libmata.nfa.nfa as mata_nfa
import libmata.alphabets as alphabets

class MSOFormula:
    def process_in_process_set(self, process_var, process_set_var):
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

        return i_in_I, symbol_map
    
    def process_set_subseteq_process_set(self, process_set_var_1, process_set_var_2):
        # construct mata automaton for I subseteq J
        I_subseteq_J = mata_nfa.Nfa(1, label=process_set_var_1 + " subseteq " + process_set_var_2)
        I_subseteq_J.make_initial_state(0)
        I_subseteq_J.add_transition(0, "00", 0)
        I_subseteq_J.add_transition(0, "01", 0)
        I_subseteq_J.add_transition(0, "11", 0)
        I_subseteq_J.make_final_state(0)

        # maps indices to symbols
        symbol_map = [process_set_var_1, process_set_var_2]

        return I_subseteq_J, symbol_map
    
    def process_successor(self, predecessor, successor):
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

        return process_successor, symbol_map