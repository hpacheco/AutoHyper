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

module AutomataUtil

open System.Collections.Generic

open FsOmegaLib.SAT
open FsOmegaLib.NBA


type Lasso<'L> = { Prefix : list<'L>; Loop : list<'L> }

module Lasso =
    let length (lasso : Lasso<'L>) = lasso.Prefix.Length + lasso.Loop.Length
    
    let map (f : 'L -> 'X) (l : Lasso<'L>) =
            {
                Prefix = List.map f l.Prefix
                Loop = List.map f l.Loop
            }
    let make (ps : list<'L>) (ss : list<'L>) : Lasso<'L> =
        {
            Prefix = ps
            Loop = ss
        }

type private FoundCycle<'T> (state:'T) =
    inherit System.Exception ()  

    member this.State = state


let nestedDEFS (nba : NBA<'T, 'L>) : (Lasso<'T>) option =
    let satEdges =
        nba.Edges |> Map.map (fun _ l -> l |> List.filter (fun (g, _) -> DNF.isSat g))

    let visitedOuter = new HashSet<_>()
    let visitedInner = new HashSet<_>()

    let predDictOuter = new Dictionary<_,_>()
    let predDictInner = new Dictionary<_,_>()


    let rec ndfs target s = 
        visitedInner.Add s |> ignore 

        for (_, t) in satEdges.[s] do 
            if visitedInner.Contains t |> not then 
                // Record that we explored t via s
                predDictInner.Add(t, s)

                ndfs target t
            elif t = target then 
                // Found a cycle
                predDictInner.Add(t, s)
                raise <| FoundCycle t

    let rec dfs s = 
        visitedOuter.Add s |> ignore 

        for (_, t) in satEdges.[s] do 
            if visitedOuter.Contains t |> not then 
                // Record that we explored t via s
                predDictOuter.Add(t, s)

                dfs t 
            
        if nba.AcceptingStates.Contains s then 
            // predDictInner.Clear()
            ndfs s s

    try 
        for s in nba.InitialStates do 
            // predDictOuter.Clear()
            dfs s 
    
        None
    with 
    | :? FoundCycle<'T> as e -> 

        let w = e.State
        // Reconstruct the path 

        let rec reconstructLoop s = 
            if s = w then 
                [s]
            else 
                reconstructLoop (predDictInner.[s]) @ [s]

        let rec reconstructPrefix s = 
            if Set.contains s nba.InitialStates then 
                [s]
            else 
                reconstructPrefix (predDictOuter.[s]) @ [s]

        {
            Lasso.Prefix = 
                if Set.contains w nba.InitialStates then 
                    []
                else                 
                    reconstructPrefix (predDictOuter.[w])
            Loop = reconstructLoop (predDictInner.[w])
        }
        |> Some
    