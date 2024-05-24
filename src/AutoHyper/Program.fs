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

module Program

open System
open System.IO

open Util
open Configuration
open ModelChecking

open HyperQPTL
open CommandLineParser

let mutable raiseExceptions = false

let private writeFormulaAndSystemString
    (systemOutputPaths : list<String>)
    formulaOutputPath
    (tsStringList : list<String>)
    (formulaString : String)
    =
    (systemOutputPaths, tsStringList)
    ||> List.zip
    |> List.iter (fun (file, tsString) ->
        try
            File.WriteAllText(file, tsString)
        with _ ->
            raise <| AutoHyperException $"Could not write to file %s{file}"
    )

    try
        File.WriteAllText(formulaOutputPath, formulaString)
    with _ ->
        raise <| AutoHyperException $"Could not write to file %s{formulaOutputPath}"


let private run (args : array<string>) =
    let swTotal = System.Diagnostics.Stopwatch()
    let sw = System.Diagnostics.Stopwatch()
    swTotal.Start()

    sw.Restart()

    let cmdArgs =
        CommandLineParser.parseCommandLineArguments (Array.toList args)
        |> Result.defaultWith (fun err -> raise <| AutoHyperException $"%s{err}")


    let solverConfig = Configuration.getSolverConfiguration ()

    let config =
        {
            Configuration.SolverConfig = solverConfig
            ModelCheckingOptions =
                {
                    ModelCheckingOptions.ComputeBisimulation = cmdArgs.ComputeBisimulation
                    ComputeWitnesses = cmdArgs.ComputeWitnesses
                    IntermediateAutomatonSimplification = cmdArgs.IntermediateAutomatonSimplification
                    BlockProduct = true

                    Mode = cmdArgs.Mode
                }
            Logger =
                {
                    Logger.Log =
                        fun s ->
                            if cmdArgs.LogPrintouts then
                                printf $"%s{s}"
                }
            RaiseExceptions = cmdArgs.RaiseExceptions
        }

    raiseExceptions <- cmdArgs.RaiseExceptions

    config.Logger.LogN $"========================= Initialization ========================="

    let systemInputPaths, formulaInputPath =
        cmdArgs.InputFiles
        |> Option.defaultWith (fun () -> raise <| AutoHyperException "No input files given")

    let tsList, formula =
        match cmdArgs.InputType with
        | SymbolicSystem ->
            config.Logger.LogN $"> Parsing model-checking instance (--nusmv)..."
            sw.Restart()

            let systemList, formula =
                InstanceParsing.readAndParseSymbolicInstance systemInputPaths formulaInputPath

            config.Logger.LogN
                $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

            config.Logger.LogN $"> Translation to explicit-state system..."
            sw.Restart()

            let tsList = Translation.convertSymbolicSystemInstance systemList formula


            config.Logger.LogN
                $"...done (time: %i{sw.ElapsedMilliseconds}ms (%.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

            tsList, formula

        | BooleanProgramSystem ->
            config.Logger.LogN $"> Parsing model-checking instance (--bp)..."
            sw.Restart()

            let programList, formula =
                InstanceParsing.readAndParseBooleanProgramInstance systemInputPaths formulaInputPath

            config.Logger.LogN
                $"...done (time: %i{sw.ElapsedMilliseconds}ms (%.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

            config.Logger.LogN $"> Translation to explicit-state system..."
            sw.Restart()

            let tsList, formula = Translation.convertBooleanProgramInstance programList formula

            config.Logger.LogN
                $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

            tsList, formula

        | ExplicitSystem ->
            config.Logger.LogN $"> Parsing model-checking instance (--explicit)..."
            sw.Restart()

            let tsList, formula =
                InstanceParsing.readAndParseExplicitInstance systemInputPaths formulaInputPath

            let tsList =
                tsList
                |> List.mapi (fun i ts ->
                    TransitionSystemLib.TransitionSystem.TransitionSystem.alignWithTypes ts
                    |> Result.defaultWith (fun err ->
                        raise
                        <| AutoHyperException
                            $"Could not infer variable evaluation in the {i}th transition system: {err}"
                    )
                )

            config.Logger.LogN
                $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

            tsList, formula

    config.Logger.LogN
        ("> system-sizes: [" + (tsList |> List.map (fun ts -> string ts.States.Count) |> String.concat "," ) + "]")

    let traceVarList = HyperQPTL.quantifiedTraceVariables formula

    if tsList.Length <> 1 && tsList.Length <> traceVarList.Length then
        raise
        <| AutoHyperException "The number of systems does not match the number of quantified traces"

    let tsList =
        if config.ModelCheckingOptions.ComputeBisimulation then
            // Compute bisimulation quotient
            sw.Restart()

            config.Logger.LogN $"> Computing bisimulation quotients..."

            let bisim =
                tsList
                |> List.map (fun ts ->
                    TransitionSystemLib.TransitionSystem.TransitionSystem.computeBisimulationQuotient ts
                    |> fst
                )

            config.Logger.LogN(
                $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)")

            config.Logger.LogN
                ("> system-sizes: [" + (tsList |> List.map (fun ts -> string ts.States.Count) |> String.concat "," ) + "]")

            bisim
        else
            tsList


    let tsMap =
        if tsList.Length = 1 then
            traceVarList |> List.map (fun x -> x, tsList.[0]) |> Map.ofList
        else
            (traceVarList, tsList) ||> List.zip |> Map.ofList

    match ModelCheckingUtil.findErrorOnModelCheckingInstance tsMap formula with
    | None -> ()
    | Some msg -> raise <| AutoHyperException $"Error in model and/or formula: %s{msg}"

    config.Logger.LogN $"=================================================="
    config.Logger.LogN ""

    match cmdArgs.WriteExplicitInstance with
    | None -> ()
    | Some(systemOutputPaths, formulaOutputPath) ->
        config.Logger.LogN $"> Writing explicit-state instance to file"
        sw.Restart()

        if systemOutputPaths.Length <> systemInputPaths.Length then
            raise
            <| AutoHyperException "The number of output files must match the number of input"

        let tsStringList =
            tsList
            |> List.map (TransitionSystemLib.TransitionSystem.TransitionSystem.print id)

        let formulaString = HyperQPTL.print id formula

        writeFormulaAndSystemString systemOutputPaths formulaOutputPath tsStringList formulaString

        config.Logger.LogN(
            $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)")


    if cmdArgs.Verify then
        let tsMap, formula = ModelCheckingUtil.convertToHyperLTL tsMap formula

        let res, _ = ModelChecking.modelCheck config tsMap formula

        config.Logger.LogN
            $"> total-time: %i{swTotal.ElapsedMilliseconds} ms (%.4f{double (swTotal.ElapsedMilliseconds) / 1000.0}s)"

        config.Logger.LogN ""

        if res.IsSat then printfn "SAT" else printfn "UNSAT"

        if cmdArgs.ComputeWitnesses then
            match res.WitnessPaths with
            | None -> ()
            | Some lassoMap ->
                // We can assume that each DNF in this lasso is SAT

                let printList (l : list<int>) =
                    l |> List.map string |> String.concat " " |> (fun x -> "(" + x + ")")

                lassoMap.Keys
                |> Seq.iter (fun pi ->
                    let lasso = lassoMap.[pi]
                    printfn $""
                    printfn $"%s{pi}"
                    printfn $"Prefix: %s{printList lasso.Prefix}"
                    printfn $"Loop: %s{printList lasso.Loop}"
                )

    0

[<EntryPoint>]
let main args =
    try
        run args
    with
    | AutoHyperException err ->
        printfn "Error during the analysis:"
        printfn $"{err}"

        if raiseExceptions then
            reraise ()

        exit -1
    | e ->
        printfn "Unexpected Error during the analysis:"
        printfn $"{e.Message}"

        if raiseExceptions then
            reraise ()

        exit -1
