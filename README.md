# AutoHyper: Explicit-State Model Checking for HyperLTL

This repository contains **AutoHyper** (short for either "**Auto**mata-based Model Checking of **Hyper**LTL" or "Fully **Auto**matic **Hyper**LTL Model Checking"), a tool that can model check HyperLTL properties on finite-state systems. 


Clone this repository and **initialize all submodules** by running 

```shell
git clone https://github.com/AutoHyper/autohyper
cd autohyper
git submodule init
git submodule update
```

When pulling a new version, make sure to update the submodules by re-running `git submodule update`.

## Overview

AutoHyper reads a transition system and a [HyperLTL](https://doi.org/10.1007/978-3-642-54792-8_15) property and determines if the property holds on the given system.
The system can either be provided as an explicit-state system or a symbolic system that is internally converted to an explicit-state representation.
Support for symbolic systems includes a fragment of the [NuSMV specification language](https://nusmv.fbk.eu/NuSMV/userman/v26/nusmv.pdf) and programs in a simple boolean programming language [2, 4].
You can read the details in our paper:

> AutoHyper: Explicit-State Model Checking for HyperLTL. Raven Beutner and Bernd Finkbeiner. TACAS 2023. [1]



### Update

The newest version of AutoHyper adds support for relational expressions as atomic HyperLTL formulas (for example, you can write `x_pi > x_pii` to state that the integer-valued variable `x` on trace `pi` is larger than on trace `pii`).
AutoHyper's model-checking algorithm now tracks these relational atoms as succinctly as possible and avoids an unfolding. 
As a consequence, the input format for AutoHyper changes slightly compared to previous versions. 
Moreover, AutoHyper now also supports HyperQPTL formulas (i.e., HyperLTL formulas with additional propositional quantification) by integrating the earlier tool AutoHyperQ [5] (now deprecated).



## Structure 

- `src/` contains the source code of AutoHyper (written in F#).
- `benchmarks/` contains various HyperLTL benchmarks and scripts to run them automatically. Most benchmarks were created by [3] for the bounded model checker [HyperQB](https://github.com/TART-MSU/HyperQB) and simply adapted to the syntax supported by AutoHyper. See `benchmarks/BenchmarkDetails.md` for more information.
- `app/` is the target folder for the build. The final AutoHyper executable will be placed here. 

## Build AutoHyper

### Dependencies

We require the following dependencies:

- [.NET 8 SDK](https://dotnet.microsoft.com/en-us/download) (tested with version 7.0.302)
- [spot](https://spot.lrde.epita.fr/) (tested with version 2.12). To make use of the latest inclusion checking options and use the `--incl-forq` option, you should install at least version 2.12 (released 2024-05-14).

Install the .NET SDK (see [here](https://dotnet.microsoft.com/en-us/download) for details) and make sure it is installed correctly by running `dotnet --version`.
Download and build spot (details can be found [here](https://spot.lrde.epita.fr/)). 
You can place the spot executables in any location of your choosing. 
To use AutoHyper you need to provide it with the *absolute* path to spot (see details below).

### Build AutoHyper

To build AutoHyper run the following (when in the main directory of this repository).

```shell
cd src/AutoHyper
dotnet build -c "release" -o ../../app
cd ../..
```

Afterward, the AutoHyper executable is located in the `app/` folder.
The AutoHyper executable is not standalone and requires the other files located in the `app/` folder (as is usual for .NET applications).
Moreover, it will only run on systems that have the .NET Core Runtime installed. 
Test that everything works as expected by running 

```shell
app/AutoHyper --version
```

### Connect spot to AutoHyper

AutoHyper requires the *autfilt* and *ltl2tgba* tools from the [spot](https://spot.lrde.epita.fr/) library.
AutoHyper is designed such that it only needs the **absolute** path to these executables, so they can be installed and placed at whatever location fits best.
The absolute paths are specified in a `paths.json` configuration file. 
This file must be located in the same directory as the AutoHyper executable (this convention makes it easy to find the config file, independent of the relative path AutoHyper is called from). 
We provide a template file `app/paths.json` that *needs to be modified*. 
After having built spot, paste the absolute path to the *autfilt* and *ltl2tgba* executables to the `paths.json` file. 
For example, if `/usr/bin/autfilt` and `/usr/bin/ltl2tgba` are the *autfilt* and *ltl2tgba* executables, respectively, the content of `app/paths.json` should be

```json
{
    "autfilt":"/usr/bin/autfilt",
    "ltl2tgba":"/usr/bin/ltl2tgba"
}
```

### A First Example

To test that the paths have been setup correctly, we can verify our first instance by running

```shell
app/AutoHyper --bp ./benchmarks/bp/concur_p1_1bit.txt ./benchmarks/bp/gni.txt
```

which should return `SAT`.

### Setup Additional Solver

In addition to spot, AutoHyper also supports the [rabit](https://github.com/iscas-tis/RABIT), [bait](https://github.com/parof/bait), and [forklift](https://github.com/Mazzocchi/FORKLIFT) inclusion checkers. 
The algorithm underlying forklift [6] is also implemented in spot (version 2.12), so you can use the forklift algorithm without installing forklift.
These tools are optional and will only be used when the appropriate mode is set (see the Section [Command Line Arguments](#command-line-arguments))
Rabit, bait, and forklift are written in Java and AutoHyper requires the absolute path to the `.jar` file of each solver. 
The content of the `paths.json` is then 

```json
{
    "autfilt":"<...>/autfilt",
    "ltl2tgba":"<...>/ltl2tgba",
    "bait":"<...>/bait.jar",
    "rabit":"<...>/rabit.jar",
    "forklift":"<...>/forklift.jar"
}
```

You can also only provide only some of the solver paths.
If you use some inclusion checker but have not specified a path to the corresponding solver, AutoHyper will raise an error.


## Run AutoHyper

After having built AutoHyper and all its dependencies, you are ready to use AutoHyper.
You can run AutoHyper by running 

```
app/AutoHyper <options> <systemPath(s)> <formulaPath>
```

where `<options>` are the command line arguments (discussed in detail below), `<systemPath(s)>` are the path(s) to the systems, and '<formulaPath>' is the path to the HyperLTL formula.
We give details on the command line options and the input format for each input mode in Section [Input for AutoHyper](#input-for-autohyper). 

## Input for AutoHyper

In this section, we first discuss the command-line options of AutoHyper, followed by the structure of supported input. 
Every call to AutoHyper has the form 

```shell
app/AutoHyper <options> <systemPath(s)> <formulaPath>
```

where `<options>` are the command line arguments (discussed in detail below), `<systemPath(s)>` are the path(s) to the systems, and '<formulaPath>' is the path to the HyperLTL formula.
Concretely, `<systemPath(s)>` can be any number of paths to systems. 
If `<systemPath(s)>` is a _single_ path, we use the provided system at this path to resolve all quantifiers. 
If `<systemPath(s)>` are _multiple_ paths, the number of provided systems must match the quantifier prefix in the HyperLTL property (specified via `<formulaPath>`).
In this case, the `i`th quantifier will be resolved on the `i`th system. 


### System Input Type

AutoHyper model-checks a HyperLTL formula (or, more generally, a HyperQPTL formula) on a given set of finite-state transition systems. 
The finite-state transition systems can be given in different input formats:

- **Explicit-state systems**, which (explicitly) define a finite set of states (identified by an integer), the transition between the states, and the evaluation of variables in each state (`--explicit`);  
- **NuSMV models**, which define a system that is defined symbolically by a set of valuables.  The transitions of the system are defined symbolically via expressions (`--nusmv`);
- **Boolean programs**, which defines a system that operates on a set of boolean variables, where the transitions are given by the semantics of the program (`--bp`). 

Depending on what input type is specified, AutoHyper interprets the systems in `<systemPath(s)>` differently. 
The next sections contain details on the input format for each type.
By default, AutoHyper assumes that the systems are given as NuSMV models. 


### Command-line Arguments

AutoHyper supports several command-line options (`<options>`):

**Model-Checking Mode:**
AutoHyper supports different model-checking strategies, based either entirely on automaton complementation or leverging language inclusion checks.
At most one of the following options can be used:

- `--comp`: Instructs AutoHyper to only rely on automaton complementation for model-checking.
- `--incl-spot`: Instructs AutoHyper to the standard inclusion check from spot. This is the default mode.
- `--incl-rabit`: Instructs AutoHyper to use the inclusion check implemented in RABIT. This mode requires a working copy of RABIT, i.e., the path to RABIT `.jar` needs to be given in `paths.json` (see Section [Setup Additional Solver](#setup-additional-solver)).
- `--incl-bait`: Instructs AutoHyper to use the inclusion check implemented in BAIT. This mode requires a working copy of BAIT, i.e., the path to BAIT `.jar` needs to be given in `paths.json` (see Section [Setup Additional Solver](#setup-additional-solver)).
- `--incl-forklift`: Instructs AutoHyper to use the inclusion check implemented in FORKLIFT. This mode requires a working copy of FORKLIFT, i.e., the path to FORKLIFT `.jar` needs to be given in `paths.json` (see Section [Setup Additional Solver](#setup-additional-solver)).
- `--incl-forq`: Instructs AutoHyper to use the FORQ-based inclusion check implemented in spot [6]. This requires at least spot version 2.12.


**Additional Options:**

- `--no-bisim`: By default AutoHyper computes a bisimulation-quotient for each system to reduce its size. This option disables the bisimulation-based preprocessing.
- `--witness`: This option instructs AutoHyper to compute witness paths for the outermost quantifier block. That is, if the formula starts with a $`\exists^*`$ block and is satisfied, AutoHyper prints concrete (lasso-shaped) witness paths for the existential quantifiers. Likewise, if the formula starts with a $`\forall^*`$ block and is _not_ satisfied, AutoHyper prints concrete (lasso-shaped) witness paths that serve as counterexamples for the universal quantifiers. If this option is used, it automatically sets the mode to `--comp` and disables bisimulation-based preprocessing (`--no-bisim`).
- `--simplification`: Instructs AutoHyper to simplify the automaton in each step using spot. 
- `--log`: Instructs AutoHyper to print additional information and more detailed error messages.
- `--version`: Displays the AutoHyper version.
- `--license`: Displays information about the license of AutoHyper.
- `--help`: Displays a help message.


### Transition Systems 

At its core, AutoHyper verifies against variable-based explicit-state transition systems. 
A variable `<var>` is any non-reserved string identifier and can have type `Int` or `Bool`. 
An explicit-state system consists of a finite set of states (identified via natural numbers), a set of initial states, and explicit transitions between these states (i.e., for each state, the system records a set of successor states).
Moreover, it maintains a set of typed variables `<var_1>, ..., <var_n>` and each state assigns each variable to a type-conforming value. 
That is, each variable `<var>` of type `Int` is mapped to an integer value, and each variable of type `Bool` is mapped to a Boolean value. 


### Specifying HyperLTL Properties

The specification checked by AutoHyper is an extension of the temporal logic HyperLTL, which uses trace variables to quantify over traces in a system. 
Formally, a trace variable `<tvar>` can be any non-empty (non-reserved) strings consisting only of letters and digits (starting with a letter).

In plain HyperLTL, each system has a finite set of Booleam atomic propositions (APs), and the body of the HyperLTL formula can refer to the APs.
We consider richer types of systems that also support integer-valued varaibles.
To support this in formulas, we consider an extension of HyperLTL where atomic formulas are arbitrary expressions over the variables found in the transition systems. 
For example, the formula `forall A. exists B. G ({"x"_A > "x"_B})` states that for all traces `A` there exists a trace `B` such that, at all times, the value of (integer-typed) variable `x` on `A` is greater than the value of `x` on `B`. 



#### Atomic Expression

Atomic expressions (`<atomicExpression>`) in HyperLTL are generated as follows:

- `true`: Represents the boolean true constant
- `false`: Represents the boolean false constant
- `<n>` where `<n>` is any integer: Represents the integer constant `<n>`
- `"<var>"_<tvar>`: Represents the value of system variable `<var>` on the trace bound to `<tvar>`. Note that the variable is escaped in `"`.
- `<atomicExpression> <opp> <atomicExpression>`: Represents a binary operation. Here `<opp>` can be: `&` (and), `|` (or), `=` (equals), `!=` (not equals), `<=` (less or equal), `>=` (greater or equal), `<` (less), `>` (greater), `+` (addition), `-` (subtraction).
- `<opp> <atomicExpression>`: Represents a unary operation. Here `<opp>` can be: `!` (boolean negation) and `-` (unary minus). 

Note that we only support well-typed atomic expressions.


#### HyperLTL Formulas

A HyperLTL formula consists of an LTL-like body, preceded by a quantifier prefix. 
Formulas have the form `<qfPrefix> <body>`.

Here `<body>` can be one of the following:

- `1`: specifies the boolean constant true
- `0`: specifies the boolean constant false
- `{<atomicExpression>}` where `<atomicExpression>` is a Boolean atomic expression. 
- `(<body>)`
- `<body> <bopp> <body>`, where `<bopp>` can be `&` (conjunction), `|` (disjunction), `->` (implication), `<->` (equivalence), `U` (until operator), `W` (weak until operator), and `R` (release operator)
- `<uopp> <body>`, where `<uopp>` can be `!` (negation), `X` (next operator), `G` (globally), and `F` (eventually operator)

The operators follow the usual operator precedences. 
To avoid ambiguity, we recommend always using parenthesis. 

The quantifier prefix `<qfPrefix>` can be one of the following:
- The empty string
- Universal quantification `forall <tvar>. <qfPrefix>`
- Existential quantification `exists <tvar>. <qfPrefix>`

An example property is the following: 

```
forall A. exists B. G ({"x"_A > "x"_B})
```

where we assumed that `x` is an integer-valued variable in the transition system(s).


### Specifying Explicit-state Transition Systems

When using option `--explicit`, AutoHyper expects an *explicit-state transition system*.
An explicit-state system has the form 

```
Variables: ("<var>" <type>) ... ("<var>" <type>)
Init: <stateID> ... <stateID> 
--BODY-- 
<stateDefinition>
...
<stateDefinition>
--END--
```

Here, 

- `<var>` is a variable (which can be any non-reserved string consisting of letters, digits, and `_`). 
- `<type>` is a type, which can be `Int` or `Bool`.
- `<stateID>` is a natural number, which we use to identify the state. 

A `<stateDefinition>` has the form 
```
State: <stateID> {("<var>" <val>) ... ("<var>" <val>)}
<stateID> ... <stateID>
```

Here, each `<val>` can either be `true`, `false`, or an integer. 

A `<stateDefinition>` defines a state by declaring its successor states and the evaluation of all variables. 
Concretely, the `{("<var>" <val>) ... ("<var>" <val>)}` defines a value for each variable.
Each variable (declared in the `Variables: ...` line) must be assigned a value that conforms to the type.
The second line lists all successors of that state.
Every state must have at least one successor state.

#### Example 

Consider the following example:

```
Variables: ("x" Int) ("y" Bool)
Init: 0 1
--BODY-- 
State: 0 {("x" 3) ("y") true}
0 2 3
State: 1 {("x" 2) ("y") true}
0 1 2
State: 2 {("x" 15) ("y") false}
0 2 3
State: 3 {("x" 1) ("y") true}
2 3
--END--
```

This specification declares states `0` and  `1` as initial states and `"x"` and `"y"` as variables of type `Int` and `Bool`, respectively.
For each state, we give the evaluation of the variables.
For example, in state `1`, variable `"x"` is assigned value `2`, and variable `"y"` is assigned value `true`.
Each state lists all successors of that node. 
For example, the successor states of state `0` are states `0`, `2`, and `3`.

#### HyperLTL Formulas in Explicit-State Systems

When specifying a system explicitly, the variables (which can be used in atomic expressions within the HyperLTL formula) are exactly the variables declared in the `Variables: ...` line.
An example property on the above example system would be:

```
forall A. exists B. G {"x"_A = "x"_B} & F {"y"_B}
```

### Specifying Symbolic Transition Systems

When using option `--nusmv` (or by default), AutoHyper expects a *NuSMV system* with finite variable domains (so the system denotes a finite-state transition system).
AutoHyper supports only a fragment of the NuSMV specification language.
In particular, we assume that the system consists of a *single module*. 
In Section [Convert To Single Module System](#convert-to-single-module-system) we give details on how to automatically convert a system into a single-module system. 


A single-module NuSMV model (as supported by AutoHyper) has the following structure:

```
MODULE main
<variableDeclarationBlock>
<bodyBlock>
```

#### Variable Declaration Block

The `<variableDeclarationBlock>` declares all variables and assigns a type. 
The variable declaration block has the form 

```
VAR 
<varName> : <type>;
<varName> : <type>;
...
<varName> : <type>;
```

containing a sequence of type assignments. 
Here `<varName>` is a variable name.
A valid variable name is any sequence of characters that starts with a letter or `_`, followed by an arbitrary sequence of letters, digits, or the special symbols `_`, `$`, `#`, `-`, `[`, `]`, `.` and is no reserved keyword.

`<type>` gives the type of that variable. 
Support types are:
- `boolean`: The boolean type with allowed values `TRUE` and `FALSE`.
- `{n_1, ..., n_M}` where `n_1`, ..., `n_m` are integers: This is a set type that can hold any natural number contained in the set.
- `l..h` where `l <= h` are integer: This range type can hold any integer between `l` and `h`. Internally, we treat it as a shorthand for `{l, l+1, ..., h-1, h}`.
- `array l..h of <type>` where `l <= h` are integer and `<type>` is an arbitrary (recursively defined) type: This array type models an array with valid indices for all integers between `l` and `h`. Internally, we eliminate arrays and instead introduce a separate variable for each position. For example, the type declaration `x : array 0..2 of boolean;` will be reduced to the type declarations `x[0] : boolean; x[1] : boolean; x[2] : boolean;`.


#### Assignments and Definitions

The `<bodyBlock>` defines the actual behavior of the system. In this block, we can pose initial conditions on all variables, describe how the variables should be updated in each step, and introduce additional (defined) shorthands. 
The `<bodyBlock>` is a sequence of assignment blocks and definition blocks, i.e., it has the form

```
<assignmentBlock>
...
<assignmentBlock>
<definitionBlock>
...
<definitionBlock>
<assignmentBlock>
...
<assignmentBlock>
...
```

where `<assignmentBlock>` and `<definitionBlock>` are defined in the following. 

##### Assignment Block

An assignment block (`<assignmentBlock>`) has the form 

```
ASSIGN 
<initOrNext>
<initOrNext>
...
<initOrNext>
```

where `<initOrNext>` poses an *initial* or *next* condition.
An `<initOrNext>` either has the form
```
init(<varName>) := <expression>;
```
or 
```
next(<varName>) := <expression>;
```
where `<varName>` is the name of a variable (the variable must be defined in the initial type declaration section) and `<expression>` is a NuSMV expression (formally defined below).
In the former case, we define all possible initial values for `<varName>`. 
The expression evaluates to a set of values (in the special case, where the expression is deterministic, it evaluates to a singleton set) and all such values are initial states of the system. 
The expression can refer to other variables, i.e., we allow initial conditions such as `init(x) := y;`.

In the latter case, the expression defines all successor values for the variable.
In each step, we evaluate the expression in the current state and assign the resulting value to `<varName>` in the next state.
As before, the expression evaluates to a set of values (in the deterministic case, a singleton set) and we consider all possible values in the next step.

In either case, the expression can refer to program variables (those defined in the type declaration section) and also *defined* variables (defined below).
There must not exist cyclic dependencies between the defined variables when evaluating the initial or next expression. 


##### Definition Block

A definition block (`<definitionBlock>`) has the form 

```
DEFINE
<definition>
<definition>
...
<definition>
```

where each `<definition>` has the form
```
<varName> := <expression>;
```
Here `<varName>` is a variable name that is *not* listed in the `<variableDeclarationBlock>`.
Intuitively, `<varName> := <expression>;` defines the variable `<varName>` as a shorthand for the expression `<expression>`.
As in the assignment block, we forbid cyclic dependencies during the evaluation of definitions.


#### Expressions

An expression is evaluated in a state `s`, i.e., a concrete mapping that maps each declared variable (defined in the `<variableDeclarationBlock>` block) to a value.
When evaluating an expression in state `s`, we compute a *set* of values (possibly a singleton set in case the expression is determinstic).
An `<expression>` can have the following forms:

- `TRUE`: the boolean true constant; evaluates to singelton set `{TRUE}`
- `FALSE`: the boolean false constant; evaluates to singelton set `{TRUE}`
- `<n>` where `<n>` is any integer: an integer constant; evaluates to singelton set `{<n>}`
- `<varName>`: a variable that is either declared in the `VAR` block or defined in a `DEFINE` block. In case `<varName>` is declared, it evaluates to `{s(<varName>)}`, i.e., the singleton set containing the value of variable `<varName>` in the current state `s`. In case `<varName>` is defined in a DEFINE block, we (recursively) evaluate the defined expression in state `s`.
- `toInt(<expression>)`: converts a boolean value to an integer; we first (recursively) evaluate the subexpression and map all `TRUE`s to `0`s and all `FALSE`s to `1`s.
- `toBool(<expression>)`: converts a integer value to a boolean; we first (recursively) evaluate the subexpression and map all `0`s to `FALSE`s and all other values to `TRUE`s.
- `case <expression>:<expression>; ... <expression>:<expression>; esac`: a case expression; During the evaluation, we search for the first `<expression>:<expression>` pair where the former expression (the guard) evaluates to singleton set `{TRUE}` and then compute the value of the second expression in that pair.
- `{ <expression>, ..., <expression>}`: a set expression; We (recursively) evaluate all subexpressions and take the union of all sets
- `<expression> <opp> <expression>`: Binary operation. Here `<opp>` can be: `&` (and), `|` (or), `->` (implies), `=` (equals), `!=` (not equals), `<=` (less or equal), `>=` (greater or equal), `<` (less), `>` (greater), `+` (addition), `-` (subtraction). We (recursively) evaluate both operants and apply each binary operation to all possible value combinations. 
- `<opp> <expression>`: Unary operation. Here `<opp>` can be: `!` (boolean negation). We (recursively) evaluate the operant and apply each unary operation to all possible values. 


#### Example 

Consider the following example:

```
MODULE main
VAR
    mutation: boolean;
    action: 0..2;
    beverage: 0..2;
    water: 0..3;


ASSIGN
    init(mutation) := {TRUE, FALSE};
    next(mutation) := {TRUE, FALSE};

    init(action) := 0;
    next(action) := {0,1,2};

    init(beverage) := 0;
    next(beverage) :=
        case
            (action=1 & !(water=0)): 1;
            TRUE: beverage;
        esac;

    init(water) := 2;
    next(water) :=
        case
            (action=1 & !(water=0)): water - 1; -- make beverage
            (mutation & water=0): 1;
            (mutation & water=1): 2;
            (mutation & water=2): 3;
            (mutation & water=3): 3;
            (!mutation & water=0): 2;
            (!mutation & water=1): 3;
            (!mutation & water=2): 3;
            (!mutation & water=3): 3;
            TRUE: water;
        esac;

DEFINE
    NO_water := (action=1) & (water=0);
    NO_output := (action!=1)  | ((action=1)&(beverage=0));
```


#### HyperLTL Formulas in Symbolic Transition Systems

When specifying a system as NuSMV systems, the variables (which can be used in atomic expressions within the HyperLTL formula) are all variables that are either declared (in the `<variableDeclarationBlock>`) or defined in some `<definitionBlock>`.
An example property on the above example system would be:

```
forall A. exists B. 
(
    ({"action"_A = "action"_B}) U ({"NO_water"_B})
)
```

Here `NO_water` is a defined boolean variable and `action` is a declared integer variable.


#### Convert To Single Module System 

The syntax supported by AutoHyper (and outlined above) does not include all NuSMV systems. 
Most importantly, we only support systems that consist of a **single module**.
Fortunately, the [NuSMV toolchain](https://nusmv.fbk.eu/) provides a function to flatten a system (called `flatten_hierarchy`), i.e., convert an arbitrary NuSMV model to one that consists of a single module. 
The result of this flatting does, in most cases, yield a NuSMV system that is supported by AutoHyper. 

To use this, install the [NuSMV toolchain](https://nusmv.fbk.eu/) (tested with version 2.6.0). 
For the easiest use, we recommend using the tool in *scripting* model.
Save the following script to a file (say `script.txt`)

```
read_model -i <input_path>;
flatten_hierarchy; 
write_flat_model -o <output_path>; 
quit;
```

where `<input_path>` is the path to the SMV model that should be flattened and `<output_path>` is the path the flattened model should be written to. 
When calling 

```shell
<...>/NuSMV -source script.txt
```
the script will be executed. 
Here `<...>/NuSMV` is the path to the NuSMV tool. 


**Python Script:**
We provide a Python script (`convertNuSMV.py`) that automates this process as much as possible. 
First, **modify** the `convertNuSMV.py` script by inserting the absolute path to the `NuSMV` executable of the NuSMV tool.
Afterward, you can call 

```
python convertNuSMV.py <file_1> ... <file_n>
```

where `<file_1>`, ..., `<file_n>` are the NuSMV files that should be converted. 
The system will save the flattened systems in files `_<file_1>`, ..., `_<file_n>`, i.e., prepend a `_` to each file name.
You can then apply AutoHyper to the flattened model (starting with a `_`).


### Specifying Boolean Programs

When using option `--bp`, AutoHyper expects a system given as a boolean program.
A boolean program operates on variables that hold a vector of boolean values (with statically bounded length). 

A boolean program has the form 
```
<header>
<statement>
```

where `<header>` and `<statement>` are defined below.

#### Header 

The `<header>` has the form 

```
<varName> : <bitwidth>;
<varName> : <bitwidth>;
...
<varName> : <bitwidth>;
```

and defines a bitwidth for each variable. 
A valid variable name (`<varName>`) is any non-empty sequence of letters. 
Each `<bitwidth>` is a natural number that defines the bitwidth of each variable. 

#### Expressions

Expressions (`<expression>`) have the form 
- `<varName>`: The value currently bound to a variable
- `t`: boolean true
- `f`: boolean false
- `<expression> & <expression>`: Pointwise conjunction. Assumes both arguments to evaluate to vectors of the same length.
- ` <expression> | <expression>`: Pointwise disjunction. Assumes both arguments to evaluate to vectors of the same length.
- `! <expression>`: Pointwise negation
- `<expression>[l, u]`: Evlautes `<expression>` and takes the bits ranging from position `l` (a natural number) to position `u` (also a natural number). You can write `<expression>[i]` as a shorthand for `<expression>[i, i]`.
- `(i * <expression>)`: Duplication where `i` is a natural number. First evaluates `<expression>` and the duplicates (concats) that vector `i` times. 

#### Statements

Statements (`<statement>`) have the form 
- `<varName> = <expression>;`: Assigns the value that `<expression>` evaluates to variable `<varName>`.
- `<varName> = *;`:  Assigns a non-deterministic value to `<varName>`.
- `if <expression> {<statement>} else {<statement>}`: Branches on whether or not `<expression>` evaluates to `[t]`.
- `<statement> <statement> ....; <statement>`: Execute all statements one after each other.
- `while <expression> {<statement>}`: Executes `<statement>` as long as `<expression>` evaluates to `[t]`.
- `if * {<statement>} else {<statement>}`: Nondeterministic branching.

Initially, all variables are assigned the constant `f` vector (of the length specified in the domain in the first line).
For details on the semantics see [2, 4].

#### Example

Consider the following example Boolean program.

```
h : 1;
l : 1;
o : 1;

o = 1 * true;
while(true) {
    h = *;
    if (h[0]) {
        o = !o;
    } else {
        o = (!o) & (h | !h);
    }
}
```

#### HyperLTL Formulas in Boolean Programs

When specifying a system as Boolean program, the variables (which can be used in atomic expressions within the HyperLTL formula) have the form `<varName>@<n>`, where `<varName>` is a variable and `<n>` a natural number. 
The variable `<varName>@<n>` has Boolean type and refers to the `<n>`th position of the vector currently assigned to `<varName>`.
An example property on the above example system would be:

```
forall A. forall B. exists C. (G ({"h@0"_A} <-> {"h@0"_C})) & (G({"l@0"_B} <-> {"l@0"_C}))
```

For further examples, take a look at the `benchmarks/bp` folder.


## References  

[1] AutoHyper: Explicit-State Model Checking for HyperLTL. Raven Beutner, Bernd Finkbeiner. TACAS 2023

[2] A Temporal Logic for Strategic Hyperproperties. Raven Beutner, Bernd Finkbeiner. CONCUR 2021

[3] Bounded Model Checking for Hyperproperties. Tzu-Han Hsu, César Sánchez, Borzoo Bonakdarpour. TACAS 2021

[4] HyperATL*: A Logic for Hyperproperties in Multi-Agent Systems. Raven Beutner, Bernd Finkbeiner. LMCS

[5] Model Checking Omega-Regular Hyperproperties with AutoHyperQ. Raven Beutner, Bernd Finkbeiner. LPAR 2023

[6] FORQ-Based Language Inclusion Formal Testing. Kyveli Doveri, Pierre Ganty, Nicolas Mazzocchi. CAV 2022
