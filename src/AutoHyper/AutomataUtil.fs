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

module AutomataUtil

open System.Collections.Generic

open FsOmegaLib.SAT
open FsOmegaLib.NBA

module private GraphUtil =

    let shortestPathsBetweenAllPairs
        (nodes : seq<'T>)
        (forwardEdges : 'T -> seq<'E * 'T>)
        (includeZeroLengthPaths : bool)
        =
        let next = new Dictionary<_, _>(Seq.length nodes * Seq.length nodes)

        for n in nodes do
            for (e, n') in forwardEdges n do
                if Seq.contains n' nodes then
                    // In case there are multiple edges we just take the first (has no impact as the length is the same)
                    if next.ContainsKey(n, n') |> not then
                        next.Add((n, n'), ([ e ], [ n; n' ]))

            if includeZeroLengthPaths then
                next.Remove((n, n)) |> ignore
                next.Add((n, n), ([], [ n ]))

        for k in nodes do
            for i in nodes do
                for j in nodes do
                    if next.ContainsKey(i, k) && next.ContainsKey(k, j) then
                        if
                            next.ContainsKey(i, j) |> not
                            || (next.[i, j] |> fst |> List.length > (next.[i, k] |> fst |> List.length)
                                                                    + (next.[k, j] |> fst |> List.length)
                                                                    + 1)
                        then
                            next.Remove((i, j)) |> ignore

                            next.Add(
                                (i, j),
                                (fst next.[i, k] @ fst next.[k, j], snd next.[i, k] @ (next.[k, j] |> snd |> List.tail))
                            )

        next


type Lasso<'L> = { Prefix : list<'L>; Loop : list<'L> }

module Lasso =
    let length (lasso : Lasso<'L>) = lasso.Prefix.Length + lasso.Loop.Length

let internal shortestAcceptingPaths (nba : NBA<'T, 'L>) =
    let satEdges =
        nba.Edges |> Map.map (fun _ l -> l |> List.filter (fun (g, _) -> DNF.isSat g))

    let res =
        GraphUtil.shortestPathsBetweenAllPairs nba.States (fun x -> satEdges.[x]) false

    let a =
        Seq.allPairs nba.InitialStates nba.AcceptingStates
        |> Seq.filter (fun (init, acc) -> (res.ContainsKey(init, acc) || init = acc) && res.ContainsKey(acc, acc))
        |> Seq.map (fun (init, acc) ->
            {
                Lasso.Prefix = if init = acc then [] else res.[init, acc] |> snd
                Loop = res.[acc, acc] |> snd
            }
        )

    if Seq.isEmpty a then
        None
    else
        a |> Seq.minBy Lasso.length |> Some
