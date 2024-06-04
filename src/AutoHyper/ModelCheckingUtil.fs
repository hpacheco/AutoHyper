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
open System.Collections.Generic

open FsOmegaLib.LTL

open TransitionSystemLib.TransitionSystem

open Util
open Configuration
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
            Map.add ("_" + q) dummySystem m
            )

    let hyperltl = 
        {
            HyperLTL.QuantifierPrefix =
                formula.QuantifierPrefix
                |> List.map (
                    function
                    | TraceQuantifier(q, pi) -> q, pi
                    | PropQuantifier(q, p) -> q, "_" + p
                )
            LTLMatrix =
                formula.LTLMatrix
                |> LTL.map (
                    AtomExpression.map (
                        function
                        | TraceAtom(var, pi) -> var, pi
                        | PropAtom p -> "a", "_" + p
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


let computeBisimulationQuotients (logger : Logger) (tsMap : Map<TraceVariable, TransitionSystemWithPrinter<string>>) = 
    let sw = System.Diagnostics.Stopwatch()

    let quotientDict = new Dictionary<_, _>()

    let bisimTsMap =
        tsMap
        |> Map.map (fun _ ts -> 
            logger.LogN $"> Computing bisimulation quotients..."
            sw.Restart()

            let bisimTs = 

                if quotientDict.ContainsKey ts.TransitionSystem then
                    let res = quotientDict.[ts.TransitionSystem]
                    logger.LogN $"  ...hashed (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"
                    res
                else
                    let bisimTs = 
                        TransitionSystemLib.TransitionSystem.TransitionSystem.computeBisimulationQuotient ts.TransitionSystem
                        |> fst

                    quotientDict.Add(ts.TransitionSystem, bisimTs)

                    logger.LogN(
                        $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)")

                    bisimTs

            {
                TransitionSystemWithPrinter.TransitionSystem = bisimTs
                Printer = Map.empty
            }
        )

    bisimTsMap

let flattenBooleanExpression (tsMap : Map<TraceVariable, TransitionSystemWithPrinter<string>>) (formula : HyperQPTL<string>) = 
    let allUnaryAtoms = 
        LTL.allAtoms formula.LTLMatrix
        |> Seq.choose (fun e -> 
            let traceVariables = 
                AtomExpression.allVars e 
                |> Seq.choose (function 
                    | TraceAtom(_, pi) -> Some pi
                    | PropAtom _ -> None
                    )
                |> Seq.distinct

            let containsPropAtom = 
                AtomExpression.allVars e 
                |> Seq.exists (function 
                    | TraceAtom _ -> false
                    | PropAtom _ -> true
                    )

            if (not containsPropAtom) && Seq.length traceVariables = 1 then 
                // The expression refers to a unique trace variable, so should be flattened
                Some (e, Seq.head traceVariables)
            else 
                None
            )

    let updatedTsMap, updatedLtlMatrix, _ = 
        ((tsMap, formula.LTLMatrix, 0), allUnaryAtoms)
        ||> Seq.fold (fun (tsMap, ltl, i) (e, pi) -> 
            
            let freshVariableName = "@" + string i

            let prevTs = tsMap.[pi].TransitionSystem
            let printer = tsMap.[pi].Printer

            // Update the TS by adding the Boolean variable `freshVariableName` as a shorthand for `e`
            let updatedTs = 
                {
                    TransitionSystem.States = prevTs.States
                    InitialStates = prevTs.InitialStates
                    VariableType = prevTs.VariableType |> Map.add freshVariableName VariableType.Bool  
                    Edges = prevTs.Edges
                    VariableEval = 
                        prevTs.VariableEval 
                        |> Map.map (fun _ varEval -> 
                            // Check if the expression holds in the given state
                            let b = 
                                e
                                |> AtomExpression.bind (function 
                                    | PropAtom _ -> failwith ""
                                    | TraceAtom (var, _) -> 
                                        // We can ignore the trace variable, as we now that it will be `pi`
                                    
                                        match varEval.[var] with
                                        | TransitionSystemLib.TransitionSystem.VariableValue.IntValue i -> IntConstant i
                                        | TransitionSystemLib.TransitionSystem.VariableValue.BoolValue b ->
                                            BoolConstant b
                                )
                                |> AtomExpression.simplify
                                |> function
                                    | BoolConstant b -> b
                                    | _ -> raise <| AutoHyperException "Atomic expression evaluate to non-Boolean value"

                            varEval
                            |> Map.add freshVariableName (VariableValue.BoolValue b)
                            )
                }

            let updatedFormula = 
                ltl 
                |> LTL.bind (fun ee -> 
                    if e = ee then 
                        // Replace the expression with the shortcut
                        Atom (AtomExpression.Variable (TraceAtom(freshVariableName, pi)))
                    else 
                        Atom ee
                    )

            Map.add pi {TransitionSystemWithPrinter.TransitionSystem = updatedTs; Printer = printer} tsMap, updatedFormula, i + 1
            )


    updatedTsMap, {HyperQPTL.QuantifierPrefix = formula.QuantifierPrefix; LTLMatrix = updatedLtlMatrix}


let unfoldAtomicExpressions (tsMap : Map<TraceVariable, TransitionSystemWithPrinter<string>>) (formula : HyperQPTL<string>) = 
    // TODO
    tsMap, formula
