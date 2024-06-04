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

open TransitionSystemLib.TransitionSystem

open Util
open Configuration
open AutomataUtil
open ModelChecking

open HyperQPTL
open CommandLineParser

let mutable raiseExceptions = false

let sw = System.Diagnostics.Stopwatch()


let private writeFormulaAndSystemString
    config
    (tsMap : Map<TraceVariable, TransitionSystem<string>>)
    formula
    =

    config.Logger.LogN $"> Writing explicit-state instance to file"
    sw.Restart()

    formula
    |> HyperQPTL.quantifiedTraceVariables
    |> List.iter (fun pi -> 
        
        let tsString = TransitionSystemLib.TransitionSystem.TransitionSystem.print id tsMap.[pi]

        let path = "sys" + "_" + pi + ".txt"

        try
            File.WriteAllText(path, tsString)
        with _ ->
            raise <| AutoHyperException $"Could not write to file %s{path}"
        )

    let formulaString = HyperQPTL.print id formula
    let formulaPath = "prop.txt"

    try
        File.WriteAllText(formulaPath, formulaString)
    with _ ->
        raise <| AutoHyperException $"Could not write to file %s{formulaPath}"

    config.Logger.LogN(
        $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)")


    


let private run (args : array<string>) =
    let swTotal = System.Diagnostics.Stopwatch()
    
    swTotal.Start()

    sw.Restart()

    let cmdArgs =
        CommandLineParser.parseCommandLineArguments (Array.toList args)
        |> Result.defaultWith (fun err -> raise <| AutoHyperException $"%s{err}")


    let solverConfig = Configuration.getSolverConfiguration ()

    let logger = 
        {
            Logger.Log =
                fun s ->
                    if cmdArgs.LogPrintouts then
                        printf $"%s{s}"
        }

    let config =
        {
            Configuration.SolverConfig = solverConfig
            ModelCheckingOptions =
                {
                    ModelCheckingOptions.ComputeBisimulation = 
                        if cmdArgs.ComputeWitnesses && cmdArgs.ComputeBisimulation then 
                            logger.LogN "! Cannot compute witnesses AND utilize bisimulation quotients"
                            logger.LogN "! We have disabled bisimulation quotients"
                            false 
                        else 
                            cmdArgs.ComputeBisimulation
                    ComputeWitnesses = cmdArgs.ComputeWitnesses
                    IntermediateAutomatonSimplification = cmdArgs.IntermediateAutomatonSimplification
                    BlockProduct = true

                    Mode = 
                        if cmdArgs.ComputeWitnesses && cmdArgs.Mode <> COMP then 
                            logger.LogN "! Cannot compute witnesses AND use inclusion checks"
                            logger.LogN "! We have switched to mode '--comp'"
                            COMP 
                        else 
                            cmdArgs.Mode
                }
            Logger = logger
                
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

            let tsList = Translation.convertSymbolicSystemInstance config.Logger systemList formula


            config.Logger.LogN
                $"...done (time: %i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

            tsList, formula

        | BooleanProgramSystem ->
            config.Logger.LogN $"> Parsing model-checking instance (--bp)..."
            sw.Restart()

            let programList, formula =
                InstanceParsing.readAndParseBooleanProgramInstance systemInputPaths formulaInputPath

            config.Logger.LogN
                $"...done (time: %i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

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
                            $"Error the {i}th transition system: {err}"
                    )
                )

            let tsListWithPrinter = 
                tsList
                |> List.map (fun ts -> 
                    {
                        TransitionSystemWithPrinter.TransitionSystem = ts 
                        Printer = 
                            ts.States
                            |> Seq.map (fun x -> x, string x)
                            |> Map.ofSeq
                    }
                    )

            config.Logger.LogN
                $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

            tsListWithPrinter, formula

    config.Logger.LogN
        ("> system-sizes: [" + (tsList |> List.map (fun ts -> string ts.TransitionSystem.States.Count) |> String.concat "," ) + "]")

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
                    {
                        TransitionSystemWithPrinter.TransitionSystem = 
                            TransitionSystemLib.TransitionSystem.TransitionSystem.computeBisimulationQuotient ts.TransitionSystem
                            |> fst
                        Printer = Map.empty
                    }
                    
                )

            config.Logger.LogN(
                $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)")

            config.Logger.LogN
                ("> system-sizes: [" + (bisim |> List.map (fun ts -> string ts.TransitionSystem.States.Count) |> String.concat "," ) + "]")

            bisim
        else
            tsList


    let tsMap =
        if tsList.Length = 1 then
            traceVarList |> List.map (fun x -> x, tsList.[0].TransitionSystem) |> Map.ofList
        else
            (traceVarList, tsList |> List.map (fun x -> x.TransitionSystem)) ||> List.zip |> Map.ofList

    let printerMap =
        if tsList.Length = 1 then
            traceVarList |> List.map (fun x -> x, tsList.[0].Printer) |> Map.ofList
        else
            (traceVarList, tsList |> List.map (fun x -> x.Printer)) ||> List.zip |> Map.ofList

    match ModelCheckingUtil.findErrorOnModelCheckingInstance tsMap formula with
    | None -> ()
    | Some msg -> raise <| AutoHyperException $"Error in model and/or formula: %s{msg}"

    config.Logger.LogN $"=================================================="
    config.Logger.LogN ""

    if cmdArgs.WriteExplicitInstance then
        writeFormulaAndSystemString config tsMap formula


    if cmdArgs.Verify then
        let tsMap, formula = ModelCheckingUtil.convertToHyperLTL tsMap formula

        let res, _ = ModelChecking.modelCheck config tsMap formula

        config.Logger.LogN
            $"> total-time: %i{swTotal.ElapsedMilliseconds} ms (%.4f{double (swTotal.ElapsedMilliseconds) / 1000.0}s)"

        config.Logger.LogN ""

    
        if cmdArgs.ComputeWitnesses then
            match res.WitnessPaths with
            | None -> ()
            | Some lassoMap ->
                // We can assume that each DNF in this lasso is SAT

                let printLasso (pi) (lasso : Lasso<int>) =
                    let printList l = 
                        l 
                        |> List.map (fun x -> printerMap.[pi].[x]) 
                        |> String.concat " " 
                        |> (fun x -> "(" + x + ")")
                    
                    $"{pi}: {printList lasso.Prefix} {printList lasso.Loop}"

                printfn $"======= Witnesses ======="
                lassoMap.Keys
                |> Seq.iter (fun pi ->
                    let lasso = lassoMap.[pi]
                    
                    printfn $"%s{printLasso pi lasso}"
                    
                )
                printfn $"=========================\n"

        if res.IsSat then printfn "SAT" else printfn "UNSAT"
    0

[<EntryPoint>]
let main args =
    try
        run args
    with
    | AutoHyperException err ->
        printfn "=========== ERROR ==========="
        printfn $"{err}"
        printfn "============================="

        if raiseExceptions then
            reraise ()

        exit -1
    | e ->
        printfn "=========== ERROR ==========="
        printfn $"{e.Message}"
        printfn "============================="

        if raiseExceptions then
            reraise ()

        exit -1
