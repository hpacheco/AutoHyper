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

module ExplicitAutomaton

open System
open System.IO
open System.Collections.Generic

open Util
open Configuration
open FsOmegaLib.NBA
open FsOmegaLib.Operations

type ExplicitNBA<'T, 'L when 'T : comparison> =
    {
        States : Set<'T>
        InitialState : 'T
        Alphabet : list<'L>
        Edges : Map<'T, list<int * 'T>>
        AcceptingStates : Set<'T>
    }

module ExplicitNBA =
    let convertStatesToInt (nba : ExplicitNBA<'T, 'L>) =
        let idDict = nba.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq

        {
            ExplicitNBA.States = nba.States |> Set.map (fun x -> idDict.[x])

            InitialState = idDict.[nba.InitialState]

            Alphabet = nba.Alphabet

            Edges =
                nba.Edges
                |> Map.toSeq
                |> Seq.map (fun (k, v) -> idDict.[k], List.map (fun (g, s) -> g, idDict.[s]) v)
                |> Map.ofSeq

            AcceptingStates = nba.AcceptingStates |> Set.map (fun x -> idDict.[x])
        }

    let toBAString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (nba : ExplicitNBA<'T, 'L>) =
        let s = new StringWriter()

        s.WriteLine(stateStringer (nba.InitialState))

        for n in nba.States do
            for (l, n') in nba.Edges.[n] do
                s.WriteLine(
                    alphStringer (nba.Alphabet.[l])
                    + ","
                    + stateStringer (n)
                    + "->"
                    + stateStringer (n')
                )

        for n in nba.AcceptingStates do
            s.WriteLine(stateStringer (n))

        s.ToString()

    let convertPairToExplicitNBA (config : Configuration) (nba1 : NBA<int, 'L>) (nba2 : NBA<int, 'L>) =
        assert (nba1.APs = nba1.APs)

        let hoaString1, hoaString2, revDict = AutomataUtil.stringifyAutomatonPair nba1 nba2

        let resNba1 =
            FsOmegaLib.Operations.AutomataUtil.operateHoaToNBA
                config.RaiseExceptions
                config.SolverConfig.MainPath
                config.SolverConfig.AutfiltPath
                [ "--split-edges" ]
                Effort.HIGH
                (fun x -> revDict.[x])
                hoaString1
            |> AutomataOperationResult.defaultWith (fun err ->
                config.Logger.LogN err.DebugInfo
                raise <| AutoHyperException err.Info
            )

        let resNba2 =
            FsOmegaLib.Operations.AutomataUtil.operateHoaToNBA
                config.RaiseExceptions
                config.SolverConfig.MainPath
                config.SolverConfig.AutfiltPath
                [ "--split-edges" ]
                Effort.HIGH
                (fun x -> revDict.[x])
                hoaString2
            |> AutomataOperationResult.defaultWith (fun err ->
                config.Logger.LogN err.DebugInfo
                raise <| AutoHyperException err.Info
            )

        assert (resNba1.InitialStates.Count = 1)
        assert (resNba2.InitialStates.Count = 1)


        let resNba1, resNba2 = FsOmegaLib.NBA.NBA.bringPairToSameAPs resNba1 resNba2

        let alphabetDict = new Dictionary<_, _>()
        let mutable currentId = 0

        let getId dnf =
            if dnf = [ [] ] then
                // This is the true DNF, we need to unfold it explicitly after the processing is done
                -1
            elif alphabetDict.ContainsKey dnf then
                alphabetDict.[dnf]
            else
                let res = currentId
                currentId <- currentId + 1
                alphabetDict.Add(dnf, res)
                res

        let edges1 =
            resNba1.Edges |> Map.map (fun _ l -> l |> List.map (fun (g, t) -> getId g, t))

        let edges2 =
            resNba2.Edges |> Map.map (fun _ l -> l |> List.map (fun (g, t) -> getId g, t))

        let alphabet = [ 0 .. currentId - 1 ]


        // Unfold all the true edges
        let edges1 =
            edges1
            |> Map.map (fun _ l ->
                l
                |> List.collect (fun (g, t) ->
                    if g = -1 then
                        // This is a true edge, replace it with all possible letters
                        alphabet |> List.map (fun l -> l, t)
                    else
                        [ g, t ]
                )
            )

        let edges2 =
            edges2
            |> Map.map (fun _ l ->
                l
                |> List.collect (fun (g, t) ->
                    if g = -1 then
                        // This is a true edge, replace it with all possible letters
                        alphabet |> List.map (fun l -> l, t)
                    else
                        [ g, t ]
                )
            )

        let explicitNba1 =
            {
                ExplicitNBA.States = resNba1.States
                InitialState = resNba1.InitialStates |> Seq.head
                Alphabet = [ 0 .. currentId - 1 ]
                Edges = edges1
                AcceptingStates = resNba1.AcceptingStates
            }

        let explicitNba2 =
            {
                ExplicitNBA.States = resNba2.States
                InitialState = resNba2.InitialStates |> Seq.head
                Alphabet = [ 0 .. currentId - 1 ]
                Edges = edges2
                AcceptingStates = resNba2.AcceptingStates
            }

        explicitNba1, explicitNba2


module AutomataChecks =

    exception private AutomatonCheckException of FsOmegaLibError

    let checkNBAContainmentBait debug mainPath baitPath (enba1 : ExplicitNBA<int, 'L>) (enba2 : ExplicitNBA<int, 'L>) =
        try
            assert (enba1.Alphabet = enba2.Alphabet)

            let alphMapper =
                enba1.Alphabet |> List.mapi (fun i x -> x, "l" + string i) |> Map.ofList

            let s1 = ExplicitNBA.toBAString string (fun x -> alphMapper.[x]) enba1
            let s2 = ExplicitNBA.toBAString string (fun x -> alphMapper.[x]) enba2

            let path1 = Path.Combine [| mainPath; "aut1.ba" |]
            let path2 = Path.Combine [| mainPath; "aut2.ba" |]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "-jar " + baitPath + " -a " + path1 + " -b " + path2
            let res = Util.SubprocessUtil.executeSubprocess Map.empty "java" arg

            match res with
            | {
                  ExitCode = 0
                  Stderr = ""
                  Stdout = c
              }
            | {
                  ExitCode = 1
                  Stderr = ""
                  Stdout = c
              } ->
                if c.Contains "Inclusion holds: true" then
                    FsOmegaLib.Operations.AutomataOperationResult.Success true
                elif c.Contains "Inclusion holds: false" then
                    FsOmegaLib.Operations.AutomataOperationResult.Success false
                else
                    FsOmegaLib.Operations.AutomataOperationResult.Fail
                        {
                            Info = $"Error by BAIT"
                            DebugInfo = $"Unexpected output by BAIT; (containment); %s{c}"
                        }
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 && exitCode <> 1 then
                    raise
                    <| AutomatonCheckException
                        {
                            Info = $"Unexpected exit code by BAIT"
                            DebugInfo = $"Unexpected exit code by BAIT; (containment); %i{exitCode}"
                        }
                else
                    raise
                    <| AutomatonCheckException
                        {
                            Info = $"Error by BAIT"
                            DebugInfo = $"Error by BAIT; (containment); %s{stderr}"
                        }

        with
        | _ when debug -> reraise ()
        | AutomatonCheckException err -> Fail(err)
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error; (BAIT, containment); %s{e.Message}"
                }

    let checkNBAContainmentRabit
        (debug : bool)
        mainPath
        rabitPath
        (enba1 : ExplicitNBA<'T, 'L>)
        (enba2 : ExplicitNBA<'T, 'L>)
        =
        try
            assert (enba1.Alphabet = enba2.Alphabet)

            let alphMapper =
                enba1.Alphabet |> List.mapi (fun i x -> x, "l" + string i) |> Map.ofList

            let s1 = ExplicitNBA.toBAString string (fun x -> alphMapper.[x]) enba1
            let s2 = ExplicitNBA.toBAString string (fun x -> alphMapper.[x]) enba2

            let path1 = Path.Combine [| mainPath; "aut1.ba" |]
            let path2 = Path.Combine [| mainPath; "aut2.ba" |]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "-jar " + rabitPath + " " + path1 + " " + path2 + " -fast"

            let res = Util.SubprocessUtil.executeSubprocess Map.empty "java" arg

            match res with
            | {
                  ExitCode = 0
                  Stderr = ""
                  Stdout = c
              }
            | {
                  ExitCode = 1
                  Stderr = ""
                  Stdout = c
              } ->
                if c.Contains "Not included." then
                    FsOmegaLib.Operations.AutomataOperationResult.Success false
                elif c.Contains "Included." then
                    FsOmegaLib.Operations.AutomataOperationResult.Success true
                else
                    FsOmegaLib.Operations.AutomataOperationResult.Fail
                        {
                            Info = $"Error by RABIT"
                            DebugInfo = $"Unexpected output by RABIT; (containment); %s{c}"
                        }
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 && exitCode <> 1 then
                    raise
                    <| AutomatonCheckException
                        {
                            Info = $"Unexpected exit code by RABIT"
                            DebugInfo = $"Unexpected exit code by RABIT;  (containsment); %i{exitCode}"
                        }
                else
                    raise
                    <| AutomatonCheckException
                        {
                            Info = $"Error by RABIT"
                            DebugInfo = $"Error by RABIT; (containment); %s{stderr}"
                        }

        with
        | _ when debug -> reraise ()
        | AutomatonCheckException err -> Fail(err)
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error; (RABIT, containment); %s{e.Message}"
                }

    let checkNBAContainmentForklift
        debug
        mainPath
        forkliftPath
        (enba1 : ExplicitNBA<'T, 'L>)
        (enba2 : ExplicitNBA<'T, 'L>)
        =
        try
            assert (enba1.Alphabet = enba2.Alphabet)

            let alphMapper =
                enba1.Alphabet |> List.mapi (fun i x -> x, "l" + string i) |> Map.ofList

            let s1 = ExplicitNBA.toBAString string (fun x -> alphMapper.[x]) enba1
            let s2 = ExplicitNBA.toBAString string (fun x -> alphMapper.[x]) enba2

            let path1 = Path.Combine [| mainPath; "aut1.ba" |]
            let path2 = Path.Combine [| mainPath; "aut2.ba" |]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "-jar " + forkliftPath + " " + path1 + " " + path2
            let res = Util.SubprocessUtil.executeSubprocess Map.empty "java" arg

            match res with
            | {
                  ExitCode = 0
                  Stderr = ""
                  Stdout = c
              }
            | {
                  ExitCode = 1
                  Stderr = ""
                  Stdout = c
              } ->
                if c.Contains "OUTPUT:false" then
                    FsOmegaLib.Operations.AutomataOperationResult.Success false
                elif c.Contains "OUTPUT:true" then
                    FsOmegaLib.Operations.AutomataOperationResult.Success true
                else
                    FsOmegaLib.Operations.AutomataOperationResult.Fail
                        {
                            Info = $"Error by FORKLIFT"
                            DebugInfo = $"Unexpected output by FORKLIFT; (containment); %s{c}"
                        }
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 && exitCode <> 1 then
                    raise
                    <| AutomatonCheckException
                        {
                            Info = $"Unexpected exit code by FORKLIFT"
                            DebugInfo = $"Unexpected exit code by FORKLIFT;  (containsment); %i{exitCode}"
                        }
                else
                    raise
                    <| AutomatonCheckException
                        {
                            Info = $"Error by FORKLIFT"
                            DebugInfo = $"Error by FORKLIFT; (containment); %s{stderr}"
                        }

        with
        | _ when debug -> reraise ()
        | AutomatonCheckException err -> Fail(err)
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error; (FORKLIFT, containment); %s{e.Message}"
                }
