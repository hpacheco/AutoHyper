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

module ModelChecking

open FsOmegaLib.LTL
open FsOmegaLib.NBA
open FsOmegaLib.SAT
open FsOmegaLib.Operations

open TransitionSystemLib.TransitionSystem

open Util
open Configuration
open AtomExpression
open HyperQPTL
open HyperLTL
open AutomataUtil
open ProductConstruction



let private sw = System.Diagnostics.Stopwatch()
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
        (isNegatedTarget : bool)
        =

        // If needed, we complement the NBA (otherwise, we simplify if desired)
        let nba =
            if possiblyNegatedAut.IsNegated <> isNegatedTarget then
                // Complementation is needed
                config.Logger.LogN $"> Automaton complementation..."
                sw.Restart()

                let res =
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

                config.Logger.LogN
                    $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

                config.Logger.LogN $"> size-before: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}"

                config.Logger.LogN $"> size-after: %i{res.Skeleton.States.Count}"

                res

            else if
                // No complementation is needed
                config.ModelCheckingOptions.IntermediateAutomatonSimplification
            then
                // Pass into spot (without any changes to the language) to enable easy simplification
                config.Logger.LogN $"> Automaton simplification..."
                sw.Restart()

                let res =
                    FsOmegaLib.Operations.AutomatonConversions.convertToNBA
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.AutfiltPath
                        (Effort.HIGH)
                        possiblyNegatedAut.Aut
                    |> AutomataOperationResult.defaultWith (fun err ->
                        config.Logger.LogN err.DebugInfo
                        raise <| AutoHyperException err.Info
                    )

                config.Logger.LogN
                    $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

                config.Logger.LogN $"> size-before: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}"

                config.Logger.LogN $"> size-after: %i{res.Skeleton.States.Count}"

                res
            else
                possiblyNegatedAut.Aut

        {
            PossiblyNegatedAutomaton.Aut = nba
            IsNegated = isNegatedTarget
        }


let rec private generateAutomatonUpToLastBlockRec
    (config : Configuration)
    (tsMap : Map<TraceVariable,TransitionSystem<'L>>)
    (quantifierPrefix : list<QuantifierType * TraceVariable>)
    (possiblyNegatedAut : PossiblyNegatedAutomaton<'L>)
    =

    assert (quantifierPrefix |> List.isEmpty |> not)
    assert (quantifierPrefix.[0] |> fst = FORALL)

    if List.forall (fun (q, _) -> q = FORALL) quantifierPrefix then
        // Only one block of quantifiers remaining, return the prefix
        quantifierPrefix |> List.map snd, possiblyNegatedAut
    else
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

        config.Logger.LogN(
            "============ "
            + (QuantifierType.print lastQuantifierType)
            + " ["
            + (eliminationPrefix |> List.map snd |> String.concat " ")
            + " ]. ============"
        )

        config.Logger.LogN $"> size: {possiblyNegatedAut.Aut.Skeleton.States.Count}"

        let negationTarget =
            match lastQuantifierType with
            | EXISTS -> false
            | FORALL -> true

        let modPossiblyNegatedAut =
            PossiblyNegatedAutomaton.bringToNegationTargetAndSimplify config possiblyNegatedAut negationTarget

        config.Logger.LogN $"> Start automaton-system-product..."
        sw.Restart()

        let restrictedTsMap =
                (eliminationPrefix |> List.map (fun (_, pi) -> pi, tsMap.[pi]) |> Map.ofList)

        let nextAut =
                    ProductConstruction.constructAutomatonSystemProduct modPossiblyNegatedAut.Aut restrictedTsMap
                    |> NBA.convertStatesToInt
                

        config.Logger.LogN $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"


        config.Logger.LogN $"> size: {nextAut.Skeleton.States.Count}"


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
    (tsMap : Map<TraceVariable,TransitionSystem<'L>>)
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
    config.Logger.LogN $"> Start LTL-to-NBA translation..."

    sw.Restart()

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

    config.Logger.LogN $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

    config.Logger.LogN $"> size: {aut.Skeleton.States.Count}"

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


let private checkIsEmpty (config : Configuration) (nba : NBA<'T, AtomExpression<'L * TraceVariable>>) =

    let sw : System.Diagnostics.Stopwatch = System.Diagnostics.Stopwatch()
    sw.Start()

    config.Logger.LogN "========================= Emptiness Check ========================="
    config.Logger.LogN $"> size: %i{nba.Skeleton.States.Count}"
    config.Logger.LogN $"> Start emptiness check..."

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

    config.Logger.LogN $"   ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"
    config.Logger.LogN "=================================================="
    config.Logger.LogN ""

    isEmpty


let private findAcceptingPaths
    (config : Configuration)
    (universalQuantifierPrefix : list<TraceVariable>)
    (nba : NBA<'Astate, AtomExpression<'L * TraceVariable>>)
    (nbaStateToInt : TraceVariable -> 'Astate -> int)
    =

    config.Logger.LogN "========================= Emptiness Check + Witness ========================="
    config.Logger.LogN $"> size: %i{nba.Skeleton.States.Count}"
    config.Logger.LogN $"> Start lasso search..."

    sw.Restart()
    let res = AutomataUtil.nestedDEFS nba

    config.Logger.LogN $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"
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
                        Prefix = lasso.Prefix |> List.map (fun m -> nbaStateToInt pi m)
                        Loop = lasso.Loop |> List.map (fun m -> nbaStateToInt pi m)
                    }

                pi, l
            )
            |> Map.ofList

        Some pathLassoMap
    
let findTraceProduct (nba : NBA<'T,'L>) (lasso : LassoNBA<DNF<'L>>) : Lasso<'T> option
    =

    let apIndexes : Map<int,'L> = nba.APs |> List.indexed |> List.fold (fun acc (i,n) -> Map.add i n acc) Map.empty 
    let apIndex (ap : int) : 'L = apIndexes.[ap]
    let convDnf (dnf : DNF<int>) : DNF<'L> = DNF.map apIndex dnf
        
    let rec findStates (checkVisited : bool) (visited: Set<'T>) (ps: DNF<'L> list) (i: 'T) : seq<'T list * 'T> =
        seq {
            match ps with
            | [] -> 
                yield ([], i)
            | p::ps ->
                if ((not checkVisited) || (not (Set.contains i visited))) then
                    for (dnf,next_i) in nba.Edges.[i] do
                        if (p = convDnf dnf) then
                            let visited' = Set.add i visited
                            let next = findStates false visited' ps next_i
                            let stutter = findStates true visited' (p::ps) next_i
                            for (xs, j) in Seq.append next stutter do
                                yield (i::xs, j)
        }
    
    let rec findLasso (xs: 'T list) (k: 'T) : seq<'T list * 'T list> =
        seq {
            match xs with
            | [] -> ()
            | x::xs ->
                let nexts_k = nba.Edges.[k] |> List.map snd |> Set.ofList
                let foundk = seq {
                                if Set.contains x nexts_k then
                                    yield ([], x::xs)
                            }
                let continuek = seq {
                                    for (prefix, lasso) in findLasso xs k do
                                        yield (x::prefix, lasso)
                                }
                yield! (Seq.append foundk continuek)
        }
         
    seq {
        let is = nba.InitialStates
        for (prefix', j) in Seq.collect (findStates false Set.empty lasso.Prefix) is do
            for (suffix', k) in findStates false (Set.ofList prefix') lasso.Cycle j do
                for (prefix'', suffix'') in findLasso suffix' k do
                    let accepts = nba.AcceptingStates
                    if not (Set.intersect accepts (Set.ofList suffix'') |> Set.isEmpty) then
                        yield (Lasso.make (List.append prefix' prefix'') suffix'')
    }
    |> Seq.tryHead

let findTraces (restrictedTsMap : Map<TraceVariable,TransitionSystem<'L>>) (nba : NBA<Map<TraceVariable,int>, AtomExpression<'L * TraceVariable>>) (lasso : LassoNBA<DNF<AtomExpression<'L * TraceVariable>>>)
        : Map<TraceVariable, Lasso<int>>
        =
        match findTraceProduct nba lasso with
        | None -> 
            printfn $"did not find source trace for {lasso}\n in system {nba}"
            Map.empty
        | Some traces -> 
            let getTrace (k : TraceVariable) : Lasso<int> = Lasso.map (fun (vs : Map<TraceVariable,int>) -> vs.[k]) traces
            Map.fold (fun acc k _ -> Map.add k (getTrace k) acc) Map.empty restrictedTsMap

type ModelCheckingResult =
    {
        IsSat : bool
        WitnessPaths : option<Map<TraceVariable, Lasso<int>>>
    }

let noWitnessModelCheckingResult (b : bool) : ModelCheckingResult =
    {
        IsSat = b
        WitnessPaths = None
    }

let private checkInclusionByEmptiness
    (config : Configuration)
    (tsMap : Map<TraceVariable,TransitionSystem<'L>>)
    (universalQuantifierPrefix : list<TraceVariable>)
    (possiblyNegatedAut : PossiblyNegatedAutomaton<'L>)
    : ModelCheckingResult
    =

    config.Logger.LogN "========================= Compute final product for emptiness check ========================="

    // Make sure the automaton is negated, as we built the product with the outermost \forall^* block
    let modPossiblyNegatedAut =
        PossiblyNegatedAutomaton.bringToNegationTargetAndSimplify config possiblyNegatedAut true

    config.Logger.LogN $"> Start automaton-system-product..."
    sw.Restart()

    let restrictedTsMap =
        (universalQuantifierPrefix |> List.map (fun pi -> pi, tsMap.[pi]) |> Map.ofList)

    let finish (finalAut : NBA<'Astate, AtomExpression<'L * TraceVariable>>) (autStateToInt : TraceVariable -> 'Astate -> int) =

        config.Logger.LogN $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"
        
        config.Logger.LogN $"> size: {finalAut.Skeleton.States.Count}"
        config.Logger.LogN "=================================================="
        config.Logger.LogN ""
        
        assert (List.isEmpty finalAut.APs)
        
        let res =
            if not config.ModelCheckingOptions.ComputeWitnesses then
                // Just check for emptiness, we use spot for this to be more efficient
        
                let isEmpty = checkIsEmpty config finalAut
        
                // The automaton is negated, so the formula holds iff the automaton is not not empty iff the automaton is empty
                { IsSat = isEmpty; WitnessPaths = None }
            else
                // Check for emptiness and search for witness paths
        
                let acceptingPaths = findAcceptingPaths config universalQuantifierPrefix finalAut autStateToInt
        
                match acceptingPaths with
                | None ->
                    // Automaton is empty, so the formula holds (as we consider the negated automaton)
                    { IsSat = true; WitnessPaths = None }
                | Some a -> { IsSat = false; WitnessPaths = Some a }
        
        res
    
    let aut = ProductConstruction.constructAutomatonSystemProduct modPossiblyNegatedAut.Aut restrictedTsMap
    finish aut (fun pi (restrictedTsMap,_) -> restrictedTsMap.[pi])

let private checkInclusionByInclusion
    (config : Configuration)
    (tsMap : Map<TraceVariable,TransitionSystem<'L>>)
    (universalQuantifierPrefix : list<TraceVariable>)
    (possiblyNegatedAut : PossiblyNegatedAutomaton<'L>)
    (inclusionChecker : InclusionChecker)
    : ModelCheckingResult
    =

    config.Logger.LogN "========================= Inclusion Check ========================="

    if possiblyNegatedAut.IsNegated then
        printfn "! WARNING: Need to complement automaton before inclusion check"

    // Make sure the automaton is NOT negated, so we can check the outermost \forall^* block using inclusion
    let modPossiblyNegatedAut =
        PossiblyNegatedAutomaton.bringToNegationTargetAndSimplify config possiblyNegatedAut false

    let nba = modPossiblyNegatedAut.Aut

    config.Logger.LogN $"> size: {nba.States.Count}"

    config.Logger.LogN $"> Construct self-composition..."
    sw.Restart()

    let restrictedTsMap =
            (universalQuantifierPrefix |> List.map (fun pi -> pi, tsMap.[pi]) |> Map.ofList)

    let selfCompositionProduct =
                ProductConstruction.constructSelfCompositionAutomaton restrictedTsMap nba.APs
    let selfComposition = selfCompositionProduct |> NBA.convertStatesToInt
    
    config.Logger.LogN $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"

    config.Logger.LogN $"> self-composition-size: {selfComposition.States.Count}"
    
    config.Logger.LogN $"> Start inclusion check..."

    swInclusion.Start()

    sw.Restart()

    let res =
        match inclusionChecker with
        | SPOT ->
            let res = FsOmegaLib.Operations.AutomataChecks.isContained
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.AutfiltPath
                        selfComposition
                        nba
            res |> AutomataOperationResult.mapValue noWitnessModelCheckingResult

        | SPOT_FORQ ->
            let res = FsOmegaLib.Operations.AutomataChecks.isContainedForq
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.AutfiltPath
                        selfComposition
                        nba
            res |> AutomataOperationResult.mapValue noWitnessModelCheckingResult
        | ROLL ->
            if config.SolverConfig.RollJarPath |> Option.isNone then
                raise
                <| AutoHyperException "Required ROLL for inclusion check, but no path to ROLL is given"
        
            let res = FsOmegaLib.Operations.AutomataChecks.isContainedRoll
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.RollJarPath.Value
                        selfComposition
                        nba
                        config.ModelCheckingOptions.ComputeWitnesses
            res |> AutomataOperationResult.mapValue (fun (b,w) ->
                let witness = Option.map (findTraces restrictedTsMap selfCompositionProduct) w
                {
                    IsSat = b
                    WitnessPaths = witness
                }
                )
        | RABIT ->
            let enba1, enba2, backMap = ExplicitAutomaton.ExplicitNBA.convertPairToExplicitNBA config selfComposition nba
    
            if config.SolverConfig.RabitJarPath |> Option.isNone then
                raise
                <| AutoHyperException "Required RABIT for inclusion check, but no path to RABIT is given"

            let res = ExplicitAutomaton.AutomataChecks.checkNBAContainmentRabit
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.RabitJarPath.Value
                        enba1
                        enba2
                        config.ModelCheckingOptions.ComputeWitnesses
            res |> AutomataOperationResult.mapValue (fun (b,w) ->
                let witness = Option.map (findTraces restrictedTsMap selfCompositionProduct << backMap) w
                {
                    IsSat = b
                    WitnessPaths = witness
                }
                )
        | BAIT ->
            let enba1, enba2, _ = ExplicitAutomaton.ExplicitNBA.convertPairToExplicitNBA config selfComposition nba

            if config.SolverConfig.BaitJarPath |> Option.isNone then
                raise
                <| AutoHyperException "Required BAIT for inclusion check, but no path to BAIT is given"

            let res = ExplicitAutomaton.AutomataChecks.checkNBAContainmentBait
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.BaitJarPath.Value
                        enba1
                        enba2
            res |> AutomataOperationResult.mapValue noWitnessModelCheckingResult
        | FORKLIFT ->
            let enba1, enba2, backMap = ExplicitAutomaton.ExplicitNBA.convertPairToExplicitNBA config selfComposition nba

            if config.SolverConfig.ForkliftJarPath |> Option.isNone then
                raise
                <| AutoHyperException "Required FORKLIFT for inclusion check, but no path to FORKLIFT is given"

            let res = ExplicitAutomaton.AutomataChecks.checkNBAContainmentForklift
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.ForkliftJarPath.Value
                        enba1
                        enba2
                        config.ModelCheckingOptions.ComputeWitnesses
            res |> AutomataOperationResult.mapValue (fun (b,w) ->
                let witness = Option.map (findTraces restrictedTsMap selfCompositionProduct << backMap) w
                {
                    IsSat = b
                    WitnessPaths = witness
                }
                )

    swInclusion.Stop()

    config.Logger.LogN $"  ...done (%i{sw.ElapsedMilliseconds}ms, %.4f{double (sw.ElapsedMilliseconds) / 1000.0}s)"
    config.Logger.LogN "=================================================="
    config.Logger.LogN ""

    res
    |> AutomataOperationResult.defaultWith (fun err ->
        config.Logger.LogN err.DebugInfo
        raise <| AutoHyperException err.Info
    )


let modelCheck (config : Configuration) (tsMap : Map<TraceVariable,TransitionSystem<'L>>) (hyperltl : HyperLTL<'L>) =

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
        match config.ModelCheckingOptions.Mode, possiblyNegatedAut.IsNegated with
        | COMP, _ | _, true ->
            // The inclusion should be checked by complementation
            // OR The automaton is already negated, which implies that the formula is alternation-free
            // In this case, checking the formula by inclusion would require an additional complementation, and checking by taking the product is much cheaper
            
            checkInclusionByEmptiness config tsMap universalQuantifierPrefix possiblyNegatedAut
        | INCL i, false ->
            checkInclusionByInclusion config tsMap universalQuantifierPrefix possiblyNegatedAut i

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
    },
    t
