(*    
    Copyright (C) 2022-2023 Raven Beutner

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

open FsOmegaLib.LTL

open TransitionSystemLib.TransitionSystem
open TransitionSystemLib.SymbolicSystem
open TransitionSystemLib.BooleanProgramSystem

open Util
open AtomExpression
open HyperQPTL


let convertSymbolicSystemInstance (systemList : list<SymbolicSystem>) (formula : HyperQPTL<string>) : list<TransitionSystem<string>> =
    match HyperQPTL.findError formula with
    | None -> ()
    | Some msg -> raise <| AutoHyperException $"Error in the HyperQPTL formula: %s{msg}"

    systemList
    |> List.iteri (fun i p ->
        match SymbolicSystem.findError p with
        | None -> ()
        | Some msg -> raise <| AutoHyperException $"Error in the %i{i}th system: %s{msg}"
    )

    if systemList.Length <> 1 && systemList.Length <> formula.QuantifierPrefix.Length then
        raise <| AutoHyperException $"Invalid number of programs"


    let tsList =
        if systemList.Length = 1 then
            // A single system where all traces are resolved on
            let relevantIdentifierList =
                formula.LTLMatrix
                |> LTL.allAtoms
                |> Seq.map (AtomExpression.allVars)
                |> Set.unionMany
                |> Seq.choose (fun x ->
                    match x with
                    | TraceAtom(var, _) -> Some var
                    | PropAtom _ -> None
                )
                |> Seq.distinct
                |> Seq.toList

            relevantIdentifierList
            |> List.iter (fun x ->
                try
                    // We infer the type of the variable, to see if it is defined
                    TransitionSystemLib.SymbolicSystem.SymbolicSystem.inferTypeOfExpression
                        systemList.[0]
                        (TransitionSystemLib.SymbolicSystem.Expression.Var x)
                    |> ignore
                with TypeInferenceException err ->
                    raise
                    <| AutoHyperException
                        $"The identifier '{x}' is used in the HyperQPTL formula but no type for '{x}' could be inferred in the system: {err} "
            )

            SymbolicSystem.convertSymbolicSystemToTransitionSystem systemList.[0] relevantIdentifierList
            |> List.singleton
        else
            let indexMapping =
                formula
                |> HyperQPTL.quantifiedTraceVariables
                |> List.mapi (fun i pi -> pi, i)
                |> Map.ofList

            // Multiple systems, so each is resolved on a separate systems
            formula
            |> HyperQPTL.quantifiedTraceVariables
            |> List.map (fun pi ->
                let relevantIdentifierList =
                    formula.LTLMatrix
                    |> LTL.allAtoms
                    |> Seq.map (AtomExpression.allVars)
                    |> Set.unionMany
                    |> Seq.choose (fun x ->
                        match x with
                        | TraceAtom(var, pii) when pi = pii -> Some var
                        | TraceAtom _ -> None
                        | PropAtom _ -> None
                    )
                    |> Seq.distinct
                    |> Seq.toList

                let symbolicSystem = systemList.[indexMapping.[pi]]

                relevantIdentifierList
                |> List.iter (fun x ->
                    try
                        // We infer the type of the variable, to see if it is defined
                        TransitionSystemLib.SymbolicSystem.SymbolicSystem.inferTypeOfExpression
                            symbolicSystem
                            (TransitionSystemLib.SymbolicSystem.Expression.Var x)
                        |> ignore
                    with TypeInferenceException err ->
                        raise
                        <| AutoHyperException
                            $"The identifier '({x}, {pi})' is used in the HyperQPTL formula but no type for '{x}' could be inferred in the system for '{pi}': {err} "
                )

                SymbolicSystem.convertSymbolicSystemToTransitionSystem symbolicSystem relevantIdentifierList
            )

    tsList


let convertBooleanProgramInstance (progList : list<BooleanProgram>) (formula : HyperQPTL<string * int>) : list<TransitionSystem<string>> * HyperQPTL<string> =
    match HyperQPTL.findError formula with
    | None -> ()
    | Some msg -> raise <| AutoHyperException $"Error in the specification: %s{msg}"

    progList
    |> List.iteri (fun i p ->
        match BooleanProgram.findError p with
        | None -> ()
        | Some msg -> raise <| AutoHyperException $"Error in the %i{i}th system: %s{msg}"
    )

    if progList.Length <> 1 && progList.Length <> formula.QuantifierPrefix.Length then
        raise <| AutoHyperException $"Invalid number of programs"

    let tsList =
        if progList.Length = 1 then
            let prog = progList[0]

            let relevantIdentifierList =
                formula.LTLMatrix
                |> LTL.allAtoms
                |> Seq.map (AtomExpression.allVars)
                |> Set.unionMany
                |> Seq.choose (fun x ->
                    match x with
                    | TraceAtom(x, _) -> Some x
                    | PropAtom _ -> None
                )
                |> Seq.distinct
                |> Seq.toList

            relevantIdentifierList
            |> List.iter (fun (v, i) ->
                if (prog.DomainMap.ContainsKey v && i < prog.DomainMap.[v]) |> not then
                    raise
                    <| AutoHyperException
                        $"AP '(%A{v}, %i{i})' is used in the HyperQPTL formula but variable '%A{v}' does not exists or does not have not the required bit width"
            )

            BooleanProgram.convertBooleanProgramToTransitionSystem prog relevantIdentifierList
            |> List.singleton
        else
            let indexMapping =
                formula
                |> HyperQPTL.quantifiedTraceVariables
                |> List.mapi (fun i pi -> pi, i)
                |> Map.ofList


            formula
            |> HyperQPTL.quantifiedTraceVariables
            |> List.map (fun pi ->
                let relevantIdentifierList =
                    formula.LTLMatrix
                    |> LTL.allAtoms
                    |> Seq.map (AtomExpression.allVars)
                    |> Set.unionMany
                    |> Seq.choose (fun x ->
                        match x with
                        | TraceAtom(var, pii) when pi = pii -> Some var
                        | TraceAtom _ -> None
                        | PropAtom _ -> None
                    )
                    |> Seq.distinct
                    |> Seq.toList

                relevantIdentifierList
                |> List.iter (fun (v, j) ->
                    if
                        (progList.[indexMapping.[pi]].DomainMap.ContainsKey v
                         && j < progList.[indexMapping.[pi]].DomainMap.[v])
                        |> not
                    then
                        raise
                        <| AutoHyperException
                            $"AP '(%A{v}, %i{j})' is used in the HyperQPTL formula but variable '%A{v}' does not exists or does not have not the required bit width"
                )

                BooleanProgram.convertBooleanProgramToTransitionSystem
                    progList.[indexMapping.[pi]]
                    relevantIdentifierList
            )

    let mappedTs = 
        tsList
        |> List.map (TransitionSystem.mapVariables (fun (var, index) -> var + "@" + string(index)))
            
    let mappedFormula = 
        formula
        |> HyperQPTL.map (fun (var, index) -> var + "@" + string(index))

    mappedTs, mappedFormula

