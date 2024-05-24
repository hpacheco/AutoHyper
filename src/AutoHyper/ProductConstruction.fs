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

module ProductConstruction

open System.Collections.Generic

open TransitionSystemLib.TransitionSystem

open FsOmegaLib.SAT
open FsOmegaLib.AutomatonSkeleton
open FsOmegaLib.NBA

open AtomExpression
open HyperLTL

let constructAutomatonSystemProduct
    (nba : NBA<'Astate, AtomExpression<'L * TraceVariable>>)
    (tsMap : Map<TraceVariable, TransitionSystem<'L>>)
    =

    let initStates =
        tsMap
        |> Map.map (fun _ x -> x.InitialStates)
        |> Util.cartesianProductMap
        |> Seq.allPairs nba.InitialStates
        |> Seq.map (fun (autState, stateMap) -> stateMap, autState)

    let queue = new Queue<_>(initStates)

    let allStates = new HashSet<_>(initStates)
    let newEdges = new Dictionary<_, _>()

    // The APs in the new automaton will grow dynamically during the construction
    let newAps = new List<_>()

    while queue.Count <> 0 do
        let n = queue.Dequeue()
        let stateMap, autState = n

        // All possible combinations of successor states
        let sucStateMaps =
            stateMap
            |> Map.map (fun pi s -> tsMap.[pi].Edges.[s])
            |> Util.cartesianProductMap

        let sucAutStates =
            nba.Edges.[autState]
            |> List.choose (fun (g, succ) ->
                let usedIndices = DNF.atoms g

                let fixedExpressionMap =
                    usedIndices
                    |> Seq.map (fun i ->
                        let e = nba.APs.[i]

                        let fixedExpression =
                            e
                            |> AtomExpression.bind (fun (var, pi) ->
                                match Map.tryFind pi stateMap with
                                | None ->
                                    // Trace pi is currently not being eliminated
                                    Variable(var, pi)
                                | Some s ->
                                    match tsMap.[pi].VariableEval.[s].[var] with
                                    | TransitionSystemLib.TransitionSystem.VariableValue.IntValue i -> IntConstant i
                                    | TransitionSystemLib.TransitionSystem.VariableValue.BoolValue b ->
                                        BoolConstant b
                            )
                            |> AtomExpression.simplify

                        i, fixedExpression
                    )
                    |> Map.ofSeq


                // All AP expression that reduce to a boolean constant, will be fixed
                let fixingMap =
                    fixedExpressionMap
                    |> Map.toSeq
                    |> Seq.choose (fun (i, e) ->
                        match e with
                        | BoolConstant b -> Some(i, b)
                        | _ -> None
                    )
                    |> Map.ofSeq

                let guardFixed = DNF.fixValues fixingMap g

                if DNF.isSat guardFixed then
                    // We remap the guard to point to the new APs

                    let remappedGuard =
                        guardFixed
                        |> DNF.map (fun x ->
                            let e = fixedExpressionMap.[x]

                            match Seq.tryFindIndex ((=) e) newAps with
                            | Some i ->
                                // The reduced expression is already contained in the list of new AP expression, so we use the existing index
                                i
                            | None ->
                                // The reduced expression was not used so far, we add it and return the index to the expression
                                newAps.Add e
                                newAps.Count - 1
                        )

                    Some(remappedGuard, succ)
                else
                    None
            )

        let sucs =
            Seq.allPairs sucStateMaps sucAutStates
            |> Seq.map (fun (stateMap', (g, autState')) ->
                // Add states for further exploration
                if allStates.Contains(stateMap', autState') |> not then
                    allStates.Add(stateMap', autState') |> ignore
                    queue.Enqueue(stateMap', autState')

                (g, (stateMap', autState'))
            )
            |> Seq.toList

        newEdges.Add(n, sucs)

    {
        NBA.Skeleton =
            {
                AutomatonSkeleton.States = set allStates
                APs = newAps |> Seq.toList
                Edges = Util.dictToMap newEdges
            }
        InitialStates = set initStates
        AcceptingStates =
            allStates
            |> Seq.filter (fun (_, autState) -> Set.contains autState nba.AcceptingStates)
            |> set
    }
    


let constructSelfCompositionAutomaton
    (tsMap : Map<TraceVariable, TransitionSystem<'L>>)
    (expressionList : list<AtomExpression<'L * TraceVariable>>)
    =

    // Assert that all interesting aps are also aps in the transition system
    assert
        (expressionList
         |> List.forall (fun e ->
             e
             |> AtomExpression.allVars
             |> Set.forall (fun (_, pi) -> Map.containsKey pi tsMap)
         ))

    let allInitStateMaps =
        tsMap |> Map.map (fun _ ts -> ts.InitialStates) |> Util.cartesianProductMap

    let queue = new Queue<_>(allInitStateMaps)
    let newEdges = new Dictionary<_, _>()
    let allStates = new HashSet<_>(allInitStateMaps)

    while queue.Count <> 0 do
        let stateMap = queue.Dequeue()

        let guardDNF : DNF<int> =
            expressionList
            |> List.mapi (fun i e ->
                // Fix all values that are resolved on systems
                let fe =
                    e
                    |> AtomExpression.bind (fun (var, pi) ->
                        match tsMap.[pi].VariableEval.[stateMap.[pi]].[var] with
                        | TransitionSystemLib.TransitionSystem.IntValue i -> IntConstant i
                        | TransitionSystemLib.TransitionSystem.BoolValue b -> BoolConstant b
                    )
                    |> AtomExpression.simplify

                match fe with
                | BoolConstant true -> Literal.PL i |> Some
                | BoolConstant false -> Literal.NL i |> Some
                | _ ->
                    // Can be both true and false, do not include constraints
                    None
            )
            |> List.choose id
            |> List.singleton

        let allSuccessorStates =
            stateMap
            |> Map.map (fun pi s -> tsMap.[pi].Edges.[s])
            |> Util.cartesianProductMap
            |> Seq.map (fun x -> guardDNF, x)
            |> Seq.toList

        newEdges.Add(stateMap, allSuccessorStates)

        for _, stateMap' in allSuccessorStates do
            if allStates.Contains stateMap' |> not then
                allStates.Add stateMap' |> ignore
                queue.Enqueue stateMap'

    {
        NBA.Skeleton =
            {
                AutomatonSkeleton.States = set allStates
                APs = expressionList
                Edges = Util.dictToMap newEdges
            }
        InitialStates = set allInitStateMaps
        AcceptingStates = set allStates
    }
