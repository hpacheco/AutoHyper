(*    
    Copyright (C) 2022-2024 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module CommandLineParser

open System

open Util
open Configuration
open ModelChecking

open JSON

let VERSION = "2.0"

let private helpMessage =
    """
    AutoHyper (Version %s{VERSION})
    
    Copyright (C) 2022-2024 Raven Beutner
    This program comes with ABSOLUTELY NO WARRANTY.
    This is free software, and you are welcome to redistribute it
    under certain conditions; use `--license' for details.

    Usage: AutoHyper [system-options] [runtime-options] [analysis-options] [mode-options] <path-to-system> ... <path-to-system> <path-to-property>

    system-options:
    --nusmv             The systems as explicit state systems as NuSMV systems (default).
    --exp               The systems as explicit state systems.
    --bp                The systems as explicit state systems as boolean programs.

    runtime-options:
    --log               Print additional log statements.
    --license           Prints license information.
    --version               Prints the current version of AutoHyper.
    --help | -h         Show command line help.

    analysis-options:
    --witness           Attempt to compute witness paths for the outermost quantifier block.
    --no-bisim          Perform no bisimulation-based minimization of systems.
    --no-simplification Perform no simplification between product constructions.

    mode-options:
    --comp              Use complementation for inclusion checking.
    --incl-spot         Use spot's inclusion check (default).
    --incl-rabit        Use rabits's inclusion check.
    --incl-bait         Use bait's inclusion check.
    --incl-forklift     Use forklift's inclusion check.
    """

let licenseMessage =
    """
    AutoHyper (Version %s{VERSION})
                
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    
    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    
    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>
    """

type InputType =
    | SymbolicSystem
    | BooleanProgramSystem
    | ExplicitSystem

type CommandLineArguments =
    {
        InputType : InputType
        InputFiles : option<list<String> * String>
        Verify : bool
        WriteExplicitInstance : option<list<String> * String>

        Mode : Mode

        ComputeWitnesses : bool
        ComputeBisimulation : bool
        IntermediateAutomatonSimplification : bool

        LogPrintouts : bool // If set to true, we log intermediate steps to the console
        RaiseExceptions : bool // If set to true, we raise esceptions
    }

    static member Default =
        {
            InputType = SymbolicSystem
            InputFiles = None
            Verify = true
            WriteExplicitInstance = None

            Mode = INCL SPOT

            ComputeWitnesses = false
            ComputeBisimulation = true
            IntermediateAutomatonSimplification = false

            LogPrintouts = false
            RaiseExceptions = false
        }


let rec private splitByPredicate (f : 'T -> bool) (xs : list<'T>) =
    match xs with
    | [] -> [], []
    | x :: xs ->
        if f x then
            [], x :: xs
        else
            let r1, r2 = splitByPredicate f xs
            x :: r1, r2

let parseCommandLineArguments (args : list<string>) =
    let rec parseArgumentsRec (args : list<string>) (opt : CommandLineArguments) =
        match args with
        | [] -> Result.Ok opt
        | x :: xs ->
            match x with
            | "--nusmv" -> parseArgumentsRec xs { opt with InputType = SymbolicSystem }
            | "--explicit" -> parseArgumentsRec xs { opt with InputType = ExplicitSystem }
            | "--bp" ->
                parseArgumentsRec
                    xs
                    { opt with
                        InputType = BooleanProgramSystem
                    }
            //
            | "--incl-rabit" -> parseArgumentsRec xs { opt with Mode = INCL RABIT }
            | "--incl-bait" -> parseArgumentsRec xs { opt with Mode = INCL BAIT }
            | "--incl-forklift" -> parseArgumentsRec xs { opt with Mode = INCL FORKLIFT }
            | "--incl-spot" -> parseArgumentsRec xs { opt with Mode = INCL SPOT }
            | "--incl-forq" -> parseArgumentsRec xs { opt with Mode = INCL SPOT_FORQ }
            | "--comp" -> parseArgumentsRec xs { opt with Mode = COMP }
            //
            | "--write-explicit" ->
                let args, ys = splitByPredicate (fun (x : String) -> x.[0] = '-') xs

                if List.length args < 2 then
                    Result.Error "Option --write-explicit must be followed by at least two arguments"
                else
                    let propertyFile = args[args.Length - 1]
                    let systemFiles = args[0 .. args.Length - 2]

                    parseArgumentsRec
                        ys
                        { opt with
                            WriteExplicitInstance = Some(systemFiles, propertyFile)
                        }
            | "--log" -> parseArgumentsRec xs { opt with LogPrintouts = true }
            | "--no-verification" -> parseArgumentsRec xs { opt with Verify = false }
            | "--witness" -> parseArgumentsRec xs { opt with ComputeWitnesses = true }
            | "--no-bisim" -> parseArgumentsRec xs { opt with ComputeBisimulation = false }
            | "--no-simplification" ->
                parseArgumentsRec
                    xs
                    { opt with
                        IntermediateAutomatonSimplification = false
                    }
            //
            | "--help"
            | "-h" ->
                printfn $"{helpMessage}"
                exit 0
            | "--version" ->
                printfn $"AutoHyper (Version %s{VERSION})"
                exit 0
            | "--license" ->
                printfn $"{licenseMessage}"
                exit 0
            //
            | s when s <> "" && s.Trim().StartsWith "-" -> Result.Error("Option " + s + " is not supported")
            | x ->
                // When no option is given, we assume that this is the input
                if opt.InputFiles.IsSome then
                    Result.Error "Input files cannot be given more than once"
                else
                    let args, ys = splitByPredicate (fun (y : String) -> y.[0] = '-') (x :: xs)

                    if List.length args < 2 then
                        Result.Error "The input must consist of at least two arguments"
                    else
                        let propertyFile = args[args.Length - 1]
                        let systemFiles = args[0 .. args.Length - 2]

                        parseArgumentsRec
                            ys
                            { opt with
                                InputFiles = (systemFiles, propertyFile) |> Some
                            }


    parseArgumentsRec args CommandLineArguments.Default
