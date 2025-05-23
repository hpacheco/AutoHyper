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

module InstanceParsing

open System.IO

open TransitionSystemLib.TransitionSystem

open Util
open HyperQPTL

let readAndParseSymbolicInstance systemInputPaths formulaInputPath =
    let systemList =
        systemInputPaths
        |> List.map (fun x ->
            try
                File.ReadAllText x
            with _ ->
                raise <| AutoHyperException $"Could not open/read file %s{x}"
        )
        |> List.mapi (fun i s ->
            TransitionSystemLib.SymbolicSystem.Parser.parseSymbolicSystem s
            |> Result.defaultWith (fun msg ->
                raise
                <| AutoHyperException $"The %i{i}th symbolic system could not be parsed: %s{msg}"
            )
        )

    let propContent =
        try
            File.ReadAllText formulaInputPath
        with _ ->
            raise <| AutoHyperException $"Could not open/read file %s{formulaInputPath}"

    let formula =
        HyperQPTL.Parser.parseHyperQPTLSymbolicSystem propContent
        |> Result.defaultWith (fun err ->
            raise
            <| AutoHyperException $"The HyperQPTL formula could not be parsed: %s{err}"
        )

    systemList, formula


let readAndParseBooleanProgramInstance systemInputPaths formulaInputPath =
    let programList =
        systemInputPaths
        |> List.map (fun x ->
            try
                File.ReadAllText x
            with _ ->
                raise <| AutoHyperException $"Could not open/read file %s{x}"
        )
        |> List.mapi (fun i s ->
            TransitionSystemLib.BooleanProgramSystem.Parser.parseBooleanProgram s
            |> Result.defaultWith (fun msg ->
                raise
                <| AutoHyperException $"The %i{i}th boolean program could not be parsed: %s{msg}"
            )
        )

    let propContent =
        try
            File.ReadAllText formulaInputPath
        with _ ->
            raise <| AutoHyperException $"Could not open/read file %s{formulaInputPath}"

    let formula =
        HyperQPTL.Parser.parseHyperQPTLBooleanProgram propContent
        |> Result.defaultWith (fun err ->
            raise
            <| AutoHyperException $"The HyperQPTL formula could not be parsed: %s{err}"
        )
        |> HyperQPTL.map (fun (var, index) -> var + "@" + string(index))

    programList, formula

let readAndParseExplicitInstance systemInputPaths formulaInputPath =
    let explicitTsList =
        systemInputPaths
        |> List.map (fun x ->
            try
                File.ReadAllText x
            with _ ->
                raise <| AutoHyperException $"Could not open/read file %s{x}"
        )
        |> List.mapi (fun i s ->
            TransitionSystemLib.TransitionSystem.Parser.parseTransitionSystem s
            |> Result.defaultWith (fun msg ->
                raise
                <| AutoHyperException $"The %i{i}th explicit-state transition system could not be parsed: %s{msg}"
            )
        )

    let propContent =
        try
            File.ReadAllText formulaInputPath
        with _ ->
            raise <| AutoHyperException $"Could not open/read file %s{formulaInputPath}"


    let formula =
        HyperQPTL.Parser.parseHyperQPTLExplicitSystem propContent
        |> Result.defaultWith (fun msg ->
            raise
            <| AutoHyperException $"The HyperQPTL formula could not be parsed: %s{msg}"
        )

    explicitTsList, formula

let transitionSystemProduct (ts : TransitionSystem<string>) : TransitionSystem<string * TraceVariable> =
    
    let toHyper (s : string) : (string * TraceVariable) =
            let openBracket = s.IndexOf('[')
            let closeBracket = s.IndexOf(']')
            if openBracket > 0 && closeBracket > openBracket then
                let iden = s.Substring(0, openBracket)
                let proj = s.Substring(openBracket + 1, closeBracket - openBracket - 1)
                (iden, proj)
            else
                failwith $"Invalid format: %s{s}"
    
    TransitionSystem.mapVariables toHyper ts

let readAndParseExplicitInstanceProduct systemInputPaths formulaInputPath =
    let explicitTsProd =
        match systemInputPaths with
        | [systemInputPath] -> 
            let s = 
                    try
                        File.ReadAllText systemInputPath
                    with _ ->
                        raise <| AutoHyperException $"Could not open/read file %s{systemInputPath}"
            let ts =
                    TransitionSystemLib.TransitionSystem.Parser.parseTransitionSystem s
                    |> Result.defaultWith (fun msg ->
                        raise
                        <| AutoHyperException $"The product explicit-state transition system could not be parsed: %s{msg}"
                    )
            transitionSystemProduct ts
        | _ -> raise <| AutoHyperException $"Only one input should be provided"
        
    let propContent =
        try
            File.ReadAllText formulaInputPath
        with _ ->
            raise <| AutoHyperException $"Could not open/read file %s{formulaInputPath}"


    let formula =
        HyperQPTL.Parser.parseHyperQPTLExplicitSystem propContent
        |> Result.defaultWith (fun msg ->
            raise
            <| AutoHyperException $"The HyperQPTL formula could not be parsed: %s{msg}"
        )

    explicitTsProd, formula

