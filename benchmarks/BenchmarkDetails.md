# Details on Benchmarks

This file contains instructions on how to run the benchmark families used for evaluation in [1].
We assume that AutoHyper and its dependencies have already been built (see instruction in the `README.md` in the main directory).
This repository currently includes the following benchmark families:

- `symbolic_tacas2023/` contains NuSMV programs with accompanying HyperLTL specifications that model a range of different verification problems. These benchmarks were created by Hsu et al. [3] and only adopted to the syntax supported by AutoHyper. See [3] for details on the benchmarks and check out the HyperLTL bounded model checker [HyperQB](https://github.com/HyperQB/HyperQB).
- `planning_tacas2023/` contains NuSMV programs that model planning problems and HyperLTL specification that model shortest and robust path search. As for the benchmarks in `symbolic/`, these instances were developed by Hsu et al. [3].


## Execution Scripts

We provide python scripts to run each benchmark family automatically. 
For this, we assume your current directly to be `/benchmarks`.

- Run `python run_symbolic_tacas2023.py` to run the benchmarks in `symbolic_tacas2023/`.
- Run `python run_planning_tacas2023.py` to run the benchmarks in `planning_tacas2023/`.


## References  

[1] AutoHyper: Explicit-State Model Checking for HyperLTL. Raven Beutner and Bernd Finkbeiner. TACAS 2023

[2] A Temporal Logic for Strategic Hyperproperties. Raven Beutner and Bernd Finkbeiner. CONCUR 2021

[3] Bounded Model Checking for Hyperproperties. Tzu-Han Hsu, César Sánchez, and Borzoo Bonakdarpour. TACAS 2021
