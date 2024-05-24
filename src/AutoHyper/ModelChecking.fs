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

module ModelChecking

open FsOmegaLib.LTL
open FsOmegaLib.NBA
open FsOmegaLib.Operations

open TransitionSystemLib.TransitionSystem

open Util
open Configuration
open AtomExpression
open HyperQPTL
open HyperLTL
open AutomataUtil


let private swTotal = System.Diagnostics.Stopwatch()
let private swComplement = System.Diagnostics.Stopwatch()
let private swProduct = System.Diagnostics.Stopwatch()
let private swInclusion = System.Diagnostics.Stopwatch()
let private swEmptiness = System.Diagnostics.Stopwatch()
let private swLTLtoNBA = System.Diagnostics.Stopwatch()

type TimeSummary =
    {
        LTL2NBATime : int
        ProductTime : int
        InclusionTime : int
        ComplementationTime : int
        EmptinessTime : int
        TotalTime : int
    }



type PossiblyNegatedAutomaton<'L when 'L : comparison> =
    {
        Aut : NBA<int, AtomExpression<'L * TraceVariable>>
        IsNegated : bool
    }

module PossiblyNegatedAutomaton =
    let bringToNegationTargetAndSimplify
        (config : Configuration)
        (possiblyNegatedAut : PossiblyNegatedAutomaton<'L>)
        (negationTarget : bool)
        =
        let sw = System.Diagnostics.Stopwatch()
        sw.Start()

        // If needed, we complement the NBA (otherwise, we simplify if desired)
        let nba =
            if possiblyNegatedAut.IsNegated <> negationTarget then
                // Complementation is needed
                config.Logger.LogN $"Start automaton complementation..."

                
                FsOmegaLib.Operations.AutomataOperations.complementToNBA
                    config.RaiseExceptions
                    config.SolverConfig.MainPath
                    config.SolverConfig.AutfiltPath
                    (Effort.HIGH)
                    possiblyNegatedAut.Aut
                |> AutomataOperationResult.defaultWith (fun err ->  
                    config.Logger.LogN err.DebugInfo
                    raise <| AutoHyperException err.Info
                )
                
            else if
                // No complementation is needed
                config.ModelCheckingOptions.IntermediateAutomatonSimplification
            then
                config.Logger.LogN $"Start automaton simplification..."
                // Pass into spot (without any changes to the language) to enable easy simplication
                
                FsOmegaLib.Operations.AutomatonConversions.convertToNBA
                    config.RaiseExceptions
                    config.SolverConfig.AutfiltPath
                    config.SolverConfig.AutfiltPath
                    (Effort.HIGH)
                    possiblyNegatedAut.Aut
                |> AutomataOperationResult.defaultWith (fun err ->  
                    config.Logger.LogN err.DebugInfo
                    raise <| AutoHyperException err.Info
                )
            else
                config.Logger.LogN $"No automaton simplification..."
                possiblyNegatedAut.Aut

        config.Logger.LogN
            $"Done. | Automaton Size: %i{nba.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double (sw.ElapsedMilliseconds) / 1000.0}s) |"

        {
            PossiblyNegatedAutomaton.Aut = nba
            IsNegated = negationTarget
        }


let rec private generateAutomatonUpToLastBlockRec
    (config : Configuration)
    (tsMap : Map<TraceVariable, TransitionSystem<'L>>)
    (quantifierPrefix : list<QuantifierType * TraceVariable>)
    (possiblyNegatedAut : PossiblyNegatedAutomaton<'L>)
    =

    assert (quantifierPrefix |> List.isEmpty |> not)
    assert (quantifierPrefix.[0] |> fst = FORALL)

    if
        (match config.ModelCheckingOptions.Mode with
         | INCL _ -> true
         | COMP -> false)
        && (List.forall (fun (q, _) -> q = FORALL) quantifierPrefix)
    then
        // Only one block of quantifiers remaining, return the prefix
        quantifierPrefix |> List.map snd, possiblyNegatedAut
    else
        let sw = System.Diagnostics.Stopwatch()

        let lastQuantifierType = quantifierPrefix |> List.last |> fst

        let remainingPrefix, eliminationPrefix =
            if config.ModelCheckingOptions.BlockProduct then
                let startIndex =
                    quantifierPrefix
                    |> List.tryFindIndexBack (fun (q, _) -> q <> lastQuantifierType)
                    |> Option.map ((+) 1)
                    |> Option.defaultValue 0

                List.splitAt startIndex quantifierPrefix
            else
                List.splitAt (List.length quantifierPrefix - 1) quantifierPrefix

        config.Logger.LogN
            ("============ " + (QuantifierType.print lastQuantifierType) + " [" + (eliminationPrefix |> List.map snd |> String.concat " ") + " ]. ============")

        config.Logger.LogN $"Automaton Size: {possiblyNegatedAut.Aut.Skeleton.States.Count}"

        let negationTarget =
            match lastQuantifierType with
            | EXISTS -> false
            | FORALL -> true

        let modPossiblyNegatedAut =
            PossiblyNegatedAutomaton.bringToNegationTargetAndSimplify config possiblyNegatedAut negationTarget

        config.Logger.LogN $"Start automaton-system-product..."
        sw.Restart()

        let restrictedTsMap =
            eliminationPrefix |> List.map (fun (_, pi) -> pi, tsMap.[pi]) |> Map.ofList

        let nextAut =
            ProductConstruction.constructAutomatonSystemProduct modPossiblyNegatedAut.Aut restrictedTsMap
            |> NBA.convertStatesToInt

        config.Logger.LogN
            $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double (sw.ElapsedMilliseconds) / 1000.0}s) |"

        config.Logger.LogN "=================================================="
        config.Logger.LogN ""

        generateAutomatonUpToLastBlockRec
            config
            tsMap
            remainingPrefix
            {
                PossiblyNegatedAutomaton.Aut = nextAut
                IsNegated = modPossiblyNegatedAut.IsNegated
            }


let generateAutomatonUpToLastBlock
    (config : Configuration)
    (tsMap : Map<TraceVariable, TransitionSystem<'L>>)
    (quantifierPrefix : list<QuantifierType * TraceVariable>)
    (ltlBody : LTL<AtomExpression<'L * TraceVariable>>)
    =
    let startWithNegated =
        if List.isEmpty quantifierPrefix then
            false
        else
            match List.last quantifierPrefix with
            | FORALL, _ -> true
            | EXISTS, _ -> false

    let body = if startWithNegated then LTL.Not ltlBody else ltlBody

    config.Logger.LogN "========================= LTL-to-NBA ========================="
    config.Logger.LogN $"Start LTL-to-NBA translation..."
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    let aut =
        FsOmegaLib.Operations.LTLConversion.convertLTLtoNBA
            config.RaiseExceptions
            config.SolverConfig.MainPath
            config.SolverConfig.Ltl2tgbaPath
            body
        |> AutomataOperationResult.defaultWith (fun err ->  
            config.Logger.LogN err.DebugInfo
            raise <| AutoHyperException err.Info
        )

    config.Logger.LogN
        $"Done. | Automaton Size: %i{aut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double (sw.ElapsedMilliseconds) / 1000.0}s) |"

    config.Logger.LogN "=================================================="
    config.Logger.LogN ""

    generateAutomatonUpToLastBlockRec
        config
        tsMap
        quantifierPrefix
        {
            PossiblyNegatedAutomaton.Aut = aut
            IsNegated = startWithNegated
        }


let private checkIsEmpty 
    (config : Configuration) 
    (nba : NBA<'T, AtomExpression<'L * TraceVariable>>) 
    =

    let sw : System.Diagnostics.Stopwatch = System.Diagnostics.Stopwatch()
    sw.Start()

    config.Logger.LogN "========================= Emptiness Check ========================="
    config.Logger.LogN $"Automaton size: %i{nba.Skeleton.States.Count}"
    config.Logger.LogN $"Start emptiness check..."

    let isEmpty =
        FsOmegaLib.Operations.AutomataChecks.isEmpty
            config.RaiseExceptions
            config.SolverConfig.MainPath
            config.SolverConfig.AutfiltPath
            (nba |> NBA.convertStatesToInt)
        |> AutomataOperationResult.defaultWith (fun err ->  
            config.Logger.LogN err.DebugInfo
            raise <| AutoHyperException err.Info
        )

    config.Logger.LogN $"Done. | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double (sw.ElapsedMilliseconds) / 1000.0}s) |"
    config.Logger.LogN "=================================================="
    config.Logger.LogN ""

    isEmpty

    
let private findAcceptingPaths 
    (config : Configuration) 
    (universalQuantifierPrefix : list<TraceVariable>)
    (nba : NBA<Map<TraceVariable,int> * int, AtomExpression<'L * TraceVariable>>) 
    =
    let sw = System.Diagnostics.Stopwatch()

    config.Logger.LogN "========================= Emptiness Check + Witness ========================="
    config.Logger.LogN $"Automaton size: %i{nba.Skeleton.States.Count}"
    config.Logger.LogN  $"Start lasso search..."

    sw.Restart()
    let res = AutomataUtil.shortestAcceptingPaths nba

    config.Logger.LogN $"Done. | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"
    config.Logger.LogN "=================================================="
    config.Logger.LogN ""

    match res with 
    | None -> 
        // Is empty and no witness path
        None
    | Some lasso -> 
        let pathLassoMap = 
            universalQuantifierPrefix
            |> List.map (fun pi -> 

                let l = 
                    { 
                        Prefix = lasso.Prefix |> List.map (fun (m, _) -> m.[pi])
                        Loop = lasso.Loop |> List.map (fun (m, _) -> m.[pi])
                    }
                
                pi, l
                )
            |> Map.ofList

        Some pathLassoMap


type ModelCheckingResult =
    {
        IsSat : bool
        WitnessPaths : option<Map<TraceVariable,Lasso<int>>>
    }

let private checkInclusionByComplementation
    (config : Configuration)
    (tsMap : Map<TraceVariable, TransitionSystem<'L>>)
    (universalQuantifierPrefix : list<TraceVariable>)
    (possiblyNegatedAut : PossiblyNegatedAutomaton<'L>)
    =

    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    // Make sure the automaton is negated, as we built the product with the outermost \forall^* block
    let modPossiblyNegatedAut =
        PossiblyNegatedAutomaton.bringToNegationTargetAndSimplify config possiblyNegatedAut true

    config.Logger.LogN $"Start automaton-system-product..."
    sw.Restart()

    let finalAut =
        ProductConstruction.constructAutomatonSystemProduct modPossiblyNegatedAut.Aut tsMap

    config.Logger.LogN
        $"Done. | Automaton Size: %i{finalAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double (sw.ElapsedMilliseconds) / 1000.0}s) |"

    assert (List.isEmpty finalAut.APs)

    if not config.ModelCheckingOptions.ComputeWitnesses then
        // Just check for emptiness, we use spot for this to be more efficient

        let isEmpty = checkIsEmpty config finalAut

        // The automaton is negated, so the formula holds iff the automaton is not not empty iff the automaton is empty
        { IsSat = isEmpty; WitnessPaths = None }
    else
        // Check for emptiness and search for witness paths

        let acceptingPaths = findAcceptingPaths config universalQuantifierPrefix finalAut

        match acceptingPaths with 
        | None -> 
            // Automaton is empty, so the formula holds (as we consider the negated automaton)
            { IsSat = true; WitnessPaths = None }
        | Some a -> { IsSat = false; WitnessPaths = Some a }



let private checkInclusionByInclusion
    (config : Configuration)
    (tsMap : Map<TraceVariable, TransitionSystem<'L>>)
    (_ : list<TraceVariable>)
    (possiblyNegatedAut : PossiblyNegatedAutomaton<'L>)
    (inclusionChecker : InclusionChecker)
    =

    if possiblyNegatedAut.IsNegated then 
        printfn ">>>>> Warning: Need to complement automaton before inclusion check"

    // Make sure the automaton is NOT negated, so we can check the outermost \forall^* block using inclusion
    let modPossiblyNegatedAut =
        PossiblyNegatedAutomaton.bringToNegationTargetAndSimplify config possiblyNegatedAut false

    let nba = modPossiblyNegatedAut.Aut

    let selfComposition =
        ProductConstruction.constructSelfCompositionAutomaton tsMap nba.APs
        |> NBA.convertStatesToInt

    swInclusion.Start()

    let res =
        match inclusionChecker with
        | SPOT ->
            FsOmegaLib.Operations.AutomataChecks.isContained
                Util.DEBUG
                config.SolverConfig.MainPath
                config.SolverConfig.AutfiltPath
                selfComposition
                nba

        | RABIT ->
            let enba1 = ExplicitAutomaton.ExplicitNBA.convertFromSymbolicNBA selfComposition
            let enba2 = ExplicitAutomaton.ExplicitNBA.convertFromSymbolicNBA nba

            if config.SolverConfig.RabitJarPath |> Option.isNone then
                raise
                <| AutoHyperException "Required RABIT for inclusion check, but no path to RABIT is given"

            ExplicitAutomaton.AutomataChecks.checkNBAContainmentRabit
                Util.DEBUG
                config.SolverConfig.MainPath
                config.SolverConfig.RabitJarPath.Value
                enba1
                enba2
        | BAIT ->
            let enba1 = ExplicitAutomaton.ExplicitNBA.convertFromSymbolicNBA selfComposition
            let enba2 = ExplicitAutomaton.ExplicitNBA.convertFromSymbolicNBA nba

            if config.SolverConfig.BaitJarPath |> Option.isNone then
                raise
                <| AutoHyperException "Required BAIT for inclusion check, but no path to BAIT is given"

            ExplicitAutomaton.AutomataChecks.checkNBAContainmentBait
                Util.DEBUG
                config.SolverConfig.MainPath
                config.SolverConfig.BaitJarPath.Value
                enba1
                enba2
        | FORKLIFT ->
            let enba1 = ExplicitAutomaton.ExplicitNBA.convertFromSymbolicNBA selfComposition
            let enba2 = ExplicitAutomaton.ExplicitNBA.convertFromSymbolicNBA nba

            if config.SolverConfig.ForkliftJarPath |> Option.isNone then
                raise
                <| AutoHyperException "Required FORKLIFT for inclusion check, but no path to FORKLIFT is given"

            ExplicitAutomaton.AutomataChecks.checkNBAContainmentForklift
                Util.DEBUG
                config.SolverConfig.MainPath
                config.SolverConfig.ForkliftJarPath.Value
                enba1
                enba2

    swInclusion.Stop()
    
    res
    |> AutomataOperationResult.defaultWith (fun err ->  
        config.Logger.LogN err.DebugInfo
        raise <| AutoHyperException err.Info
        )


let modelCheck (config : Configuration) (tsMap : Map<TraceVariable, TransitionSystem<'L>>) (hyperltl : HyperLTL<'L>) =
    
    swTotal.Reset()
    swLTLtoNBA.Reset()
    swEmptiness.Reset()
    swInclusion.Reset()
    swProduct.Reset()
    swComplement.Reset()
    
    
    
    let negateFormula =
        match List.head hyperltl.QuantifierPrefix with
        | FORALL, _ -> false
        | EXISTS, _ -> true

    let hyperltl =
        if negateFormula then
            {
                HyperLTL.QuantifierPrefix =
                    hyperltl.QuantifierPrefix |> List.map (fun (q, pi) -> QuantifierType.flip q, pi)
                LTLMatrix = LTL.Not hyperltl.LTLMatrix
            }
        else
            hyperltl

    let universalQuantifierPrefix, possiblyNegatedAut =
        generateAutomatonUpToLastBlock config tsMap hyperltl.QuantifierPrefix hyperltl.LTLMatrix

    let res = 
        match config.ModelCheckingOptions.Mode with
        | COMP ->
            // In case we want to use complementation, we can assume that the final automaton contains no APs
            assert (List.isEmpty possiblyNegatedAut.Aut.APs)

            checkInclusionByComplementation config tsMap universalQuantifierPrefix possiblyNegatedAut
        | INCL i ->
            {
                // SAT iff the inclusion holds
                IsSat = checkInclusionByInclusion config tsMap universalQuantifierPrefix possiblyNegatedAut i
                WitnessPaths = None
            }

    let t =
        {
            TotalTime = int (swTotal.ElapsedMilliseconds)
            LTL2NBATime = int (swLTLtoNBA.ElapsedMilliseconds)
            ProductTime = int (swProduct.ElapsedMilliseconds)
            InclusionTime = int (swInclusion.ElapsedMilliseconds)
            ComplementationTime = int (swComplement.ElapsedMilliseconds)
            EmptinessTime = int (swEmptiness.ElapsedMilliseconds)
        }

    // Restore the negation that is added when converting to \forall^*.... formula
    {
        IsSat = if negateFormula then not res.IsSat else res.IsSat
        WitnessPaths = res.WitnessPaths
    }, t
