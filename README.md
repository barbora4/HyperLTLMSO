# HyperLTL(MSO) model checking

## How to run the program
To run the program use the following command in the ```src``` directory:

``` ./check.py --formula=<path_to_formula> --initial-config=<path_to_initial_automaton> --symbol_mapping=<path_to_list_of_atomic_propositions> --system_transducer=<path_to_transducer_with_system_transitions>```

## Example of the system
In token passing protocol, the system consists of a parameterized number of processes in a linear array. In the initial configuration, only the leftmost process has a token. In each step, the token can either stay at the same process, or it can be passed to its right neighbour. 

Initial configurations of this system are given as a finite automaton in ```examples/token_passing_initial_conf.mata```. Atomic proposition `t` denotes that process has a token and `n` denotes that process does not have a token:

<img src="figures/token_passing_init.png" width="250"></img>

Transitions between configurations of the systems are given as a transducer in ```examples/token_passing_system.txt```:

<img src="figures/token_passing_transducer.png" width="250"></img>

## Example of the formula
Consider a HyperLTL(MSO) formula from ```examples/token_passing_f02.txt```:

$$\forall t_1. \exists t_2. \exists i. G(t_{t_1}[i] \wedge t_{t2}[i])$$

This formula is first translated into Büchi normal form (BNF) and then an extended version of the system (with new configuration variables instead of temporal operators) is created. The corresponding formula in BNF is written below:

$$\exists i. x_1[i] \\ 
\wedge G (x_1[i] \leftrightarrow (t_{t_1}[i] \wedge t_{t_2}[i] \wedge X x_1[i])) \\
\wedge GF (x_1[i] \leftrightarrow (t_{t_1}[i] \wedge t_{t_2}[i] \wedge X x_1[i]))
$$

Initial configurations of the extended system are shown in the following figure. The original initial configurations are extended with the first part of the formula in Büchi normal form. Since there are two trace quantifiers in the formula, the automaton has two tapes with atomic propositions. There is also one extra tape for configuration and process variables. 

<img src="figures/token_passing_init_extended.png" width="300"></img>

The next figure contains the extended system transducer with the second part of the formula. Since there are no eventuality variables in the formula in BNF, this transducer also shows the set of all accepting transitions of the extended system. 

<img src="figures/token_passing_trans_extended.png" width="100%"></img>

To test this example, run

```./check.py --formula=../examples/token_passing_f02.txt --initial_config=../examples/token_passing_initial_conf.mata --symbol_mapping=../examples/token_passing_mapping.txt --system_transducer=../examples/token_passing_system.txt --invariant=../examples/token_passing_f02_invariant.txt --relation=../examples/token_passing_f02_relation.txt```