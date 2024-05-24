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

module ModelCheckingUtil

open System

open FsOmegaLib.LTL

open TransitionSystemLib.TransitionSystem

open AtomExpression
open HyperQPTL
open HyperLTL

exception private FoundError of String


let convertToHyperLTL (tsMap : Map<TraceVariable, TransitionSystem<string>>) (formula : HyperQPTL<string>) =
    let propVars = HyperQPTL.quantifiedPropVariables formula

    let dummySystem = 
        {
            TransitionSystem.States = set [0; 1]
            InitialStates = set [0; 1]
            VariableType = ["a", TransitionSystemLib.TransitionSystem.VariableType.Bool] |> Map.ofList
            Edges = [ (0, set [0; 1]); (1, set [0; 1]) ] |> Map.ofList
            VariableEval = [ (0, ["a", VariableValue.BoolValue true] |> Map.ofList); (1, ["a", VariableValue.BoolValue false] |> Map.ofList) ] |> Map.ofList
        }

    let modifiedTsMap = 
        (tsMap, propVars)
        ||> List.fold (fun m q -> 
            Map.add q dummySystem m
            )

    let hyperltl = 
        {
            HyperLTL.QuantifierPrefix =
                formula.QuantifierPrefix
                |> List.map (
                    function
                    | TraceQuantifier(q, pi) -> q, pi
                    | PropQuantifier(q, p) -> q, p
                )
            LTLMatrix =
                formula.LTLMatrix
                |> LTL.map (
                    AtomExpression.map (
                        function
                        | TraceAtom(var, pi) -> var, pi
                        | PropAtom p -> "a", p
                    )
                )
        }

    modifiedTsMap, hyperltl

    
let findErrorOnModelCheckingInstance (tsMap : Map<TraceVariable, TransitionSystem<'L>>) (formula : HyperQPTL<'L>) =
    try
        match HyperQPTL.findError formula with
        | None -> ()
        | Some msg -> raise <| FoundError $"Error in the HyperQPTL formula: %s{msg}"

        tsMap
        |> Map.iter (fun pi x ->
            match TransitionSystem.findError x with
            | None -> ()
            | Some msg ->
                raise
                <| FoundError $"Error in the transition system for trace variable {pi}: %s{msg}"
        )

        let traceVariables = HyperQPTL.quantifiedTraceVariables formula

        traceVariables
        |> List.iter (fun pi ->
            if Map.containsKey pi tsMap |> not then
                raise <| FoundError $"No system for trace variable '{pi}' was given"
        )

        formula.LTLMatrix
        |> LTL.allAtoms
        |> Set.iter (fun e ->
            let t =
                e
                |> AtomExpression.inferType (function 
                    | PropAtom _ -> AtomVariableType.Bool
                    | TraceAtom (var, pi) -> 
                        match Map.tryFind var tsMap.[pi].VariableType with
                        | None ->
                            raise
                            <| FoundError
                                $"Variable '({var}, {pi})' was used in an atomic expression but '{var}' is not declared in the system for '{pi}'"
                        | Some(TransitionSystemLib.TransitionSystem.VariableType.Bool) -> AtomVariableType.Bool
                        | Some(TransitionSystemLib.TransitionSystem.VariableType.Int) -> AtomVariableType.Int
                )

            if t <> Some Bool then
                raise <| FoundError $"Atomic expression '{AtomExpression.print (ExpressionAtom.print string) e}' does not have type 'Bool'"
        )

        None
    with FoundError msg ->
        Some msg
