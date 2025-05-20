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

module Translation

open System
open System.Collections.Generic

open FsOmegaLib.LTL

open TransitionSystemLib.TransitionSystem
open TransitionSystemLib.SymbolicSystem
open TransitionSystemLib.BooleanProgramSystem

open Util
open Configuration
open AtomExpression
open HyperQPTL

type TransitionSystemType =
    | ExplicitStateSystem of TransitionSystem<string>
    | ExplicitStateSystemProduct of TransitionSystem<string * TraceVariable>
    | SymbolicSystem of SymbolicSystem
    | BooleanProgram of BooleanProgram


let private restrictVariables (variables : Set<'L>) (ts : TransitionSystem<'L>) =
    {
        TransitionSystem.States = ts.States
        InitialStates = ts.InitialStates
        VariableType = ts.VariableType |> Map.filter (fun v _ -> Set.contains v variables)
        Edges = ts.Edges
        VariableEval =
            ts.VariableEval
            |> Map.map (fun _ m -> m |> Map.filter (fun v _ -> Set.contains v variables))
    }


let private convertSymbolicSystem (relevantIdentifierList) (sys : SymbolicSystem) =
    relevantIdentifierList
    |> List.iter (fun x ->
        try
            // We infer the type of the variable, to see if it is defined
            TransitionSystemLib.SymbolicSystem.SymbolicSystem.inferTypeOfExpression
                sys
                (TransitionSystemLib.SymbolicSystem.Expression.Var x)
            |> ignore
        with TypeInferenceException err ->
            raise
            <| AutoHyperException
                $"The identifier '{x}' is used in the HyperQPTL formula but no type for '{x}' could be inferred in the system: {err} "
    )

    SymbolicSystem.convertSymbolicSystemToTransitionSystem sys relevantIdentifierList


let private convertBooleanProgram (relevantIdentifierList : list<string>) (bp : BooleanProgram) =
    // We need to parse the string-valued variables into variables of the form '(var, i)'
    let relevantIdentifierList =
        relevantIdentifierList
        |> List.map (fun x ->
            let res = x.Split('@')

            match res with
            | [| a; b |] ->
                let i =
                    try
                        Int32.Parse b
                    with _ ->
                        raise
                        <| AutoHyperException
                            $"Variable {x} is resolved on a Boolean system but does not have the correct form (...@i)"

                (a, i)
            | _ ->
                raise
                <| AutoHyperException
                    $"Variable {x} is resolved on a Boolean system but does not have the correct form (...@i)"
        )

    relevantIdentifierList
    |> List.iter (fun (v, i) ->
        if (bp.DomainMap.ContainsKey v && i < bp.DomainMap.[v]) |> not then
            raise
            <| AutoHyperException
                $"AP '(%A{v}, %i{i})' is used in the HyperQPTL formula but variable '%A{v}' does not exists or does not have not the required bit width"
    )

    let ts =
        BooleanProgram.convertBooleanProgramToTransitionSystem bp relevantIdentifierList

    {
        TransitionSystem =
            TransitionSystem.mapVariables (fun (var, index) -> var + "@" + string (index)) ts.TransitionSystem
        Printer = ts.Printer
    }

let convertToTransitionSystems (logger : Logger) (systemMap : Map<TraceVariable, TransitionSystemType>) (formula : HyperQPTL<string>) =
    let sw = System.Diagnostics.Stopwatch()

    match HyperQPTL.findError formula with
    | None -> ()
    | Some msg -> raise <| AutoHyperException $"Error in the HyperQPTL formula: %s{msg}"

    systemMap
    |> Map.iter (fun pi s ->
        match s with
        | ExplicitStateSystem ts ->
            match TransitionSystem.findError ts with
            | None -> ()
            | Some msg -> raise <| AutoHyperException $"Error in the '{pi}' system: %s{msg}"
        | ExplicitStateSystemProduct _ -> raise <| AutoHyperException $"Product should not be converted"
        | SymbolicSystem sys ->
            match SymbolicSystem.findError logger.LogN sys with
            | None -> ()
            | Some msg -> raise <| AutoHyperException $"Error in the '{pi}' system: %s{msg}"

        | BooleanProgram bp ->
            match BooleanProgram.findError bp with
            | None -> ()
            | Some msg -> raise <| AutoHyperException $"Error in the '{pi}' system: %s{msg}"
    )

    let variablesPerTraceVariable =
        formula.LTLMatrix
        |> LTL.allAtoms
        |> Set.map AtomExpression.allVars
        |> Set.unionMany
        |> Seq.choose (
            function
            | TraceAtom(var, pi) -> Some(var, pi)
            | PropAtom _ -> None
        )
        |> Seq.groupBy snd
        |> Seq.map (fun (pi, l) -> pi, l |> Seq.map fst |> set)
        |> Map.ofSeq

    // Reverse the mapping to identify multiple trace variables that are resolved on the same system (leading to better )
    let revSystemMap =
        systemMap
        |> Map.toSeq
        |> Seq.groupBy snd
        |> Seq.map (fun (s, l) -> s, l |> Seq.map fst |> set)
        |> Map.ofSeq

    let symbolicSystemDict = new Dictionary<_, _>()
    let booleanProgramDict = new Dictionary<_, _>()


    let tsMap =
        systemMap
        |> Map.map (fun pi s ->

            let ts =
                match s with
                | ExplicitStateSystemProduct _ -> raise <| AutoHyperException $"Product should not be converted"
                | ExplicitStateSystem ts ->
                    {
                        TransitionSystemWithPrinter.TransitionSystem = ts
                        // Add a printer for each state which just prints the ID
                        Printer = ts.States |> Seq.map (fun x -> x, string x) |> Map.ofSeq
                    }

                | SymbolicSystem sys ->
                    logger.LogN $"> Translating symbolic system to explicit-state system..."
                    sw.Restart()

                    if symbolicSystemDict.ContainsKey sys then
                        let res = symbolicSystemDict.[sys]
                        logger.LogN $"  ...hashed (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"
                        res
                    else
                        // The system has not been converted yet
                        // Before the conversion, we gather all variables that will be needed on this system

                        let relevantIdentifierList =
                            revSystemMap.[SymbolicSystem sys]
                            |> Set.map (fun pi -> variablesPerTraceVariable.[pi])
                            |> Set.unionMany
                            |> Set.toList

                        let ts = convertSymbolicSystem relevantIdentifierList sys

                        logger.LogN
                            $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

                        symbolicSystemDict.Add(sys, ts)

                        ts

                | BooleanProgram bp ->
                    logger.LogN $"> Translating boolean program to explicit-state system..."
                    sw.Restart()

                    if booleanProgramDict.ContainsKey bp then
                        
                        let res = booleanProgramDict.[bp]
                        logger.LogN $"  ...hashed (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"
                        res 
                    else
                        // The system has not been converted yet
                        // Before the conversion, we gather all variables that will be needed on this system

                        let relevantIdentifierList : string list =
                            revSystemMap.[BooleanProgram bp]
                            |> Set.map (fun pi -> variablesPerTraceVariable.[pi])
                            |> Set.unionMany
                            |> Set.toList

                        let ts = convertBooleanProgram relevantIdentifierList bp

                        logger.LogN
                            $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

                        booleanProgramDict.Add(bp, ts)

                        ts

            // Restrict the variables to those that are actually used in the program
            {
                TransitionSystemWithPrinter.TransitionSystem = restrictVariables (variablesPerTraceVariable.[pi]) ts.TransitionSystem
                // Add a printer for each state which just prints the ID
                Printer = ts.Printer
            }

        )

    tsMap

let addPrinter (ts : TransitionSystem<'L>) : TransitionSystemWithPrinter<'L> =
    {
        TransitionSystemWithPrinter.TransitionSystem = ts
        // Add a printer for each state which just prints the ID
        Printer = ts.States |> Seq.map (fun x -> x, string x) |> Map.ofSeq
    }



