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

module Configuration

open System.IO

open Util
open JSON

/// Records the run configuration (the location) of each supported automaton tool
type SolverConfiguration = {
    MainPath : string
    AutfiltPath : string
    Ltl2tgbaPath : string

    BaitJarPath : option<string>
    RabitJarPath : option<string>
    ForkliftJarPath : option<string>
}

type InclusionChecker =
    | SPOT
    | RABIT
    | BAIT
    | FORKLIFT
    | SPOT_FORQ

type Mode =
    | COMP
    | INCL of InclusionChecker


type ModelCheckingOptions = 
    {
        ComputeBisimulation : bool
        ComputeWitnesses : bool // Compute witnesses or counterexamples from outermost quantifiers 
        IntermediateAutomatonSimplification : bool
        BlockProduct : bool // During the product construction, use the block of quantifier of the same type

        Mode : Mode
    }


type Logger = {
    Log : string -> unit
} with

    member this.LogN s = this.Log(s + "\n")

/// A configuration summarizes the location to each solver and a printing function that is called for all non-fatal printouts
type Configuration = {
    SolverConfig : SolverConfiguration
    ModelCheckingOptions : ModelCheckingOptions
    Logger : Logger
    RaiseExceptions : bool
}


let private parseSolverConfigurationContent (s : string) =
    match JSON.Parser.parseJsonString s with
    | Result.Error err -> raise <| AutoHyperException $"Could not parse config file: %s{err}"
    | Result.Ok x -> {
        MainPath = "./"

        Ltl2tgbaPath =
            (JSON.tryLookup "ltl2tgba" x)
            |> Option.defaultWith (fun _ -> raise <| AutoHyperException "No field 'ltl2tgba' found")
            |> JSON.tryGetString
            |> Option.defaultWith (fun _ -> raise <| AutoHyperException "Field 'ltl2tgba' must contain a string")

        AutfiltPath =
            (JSON.tryLookup "autfilt" x)
            |> Option.defaultWith (fun _ -> raise <| AutoHyperException "No field 'autfilt' found")
            |> JSON.tryGetString
            |> Option.defaultWith (fun _ -> raise <| AutoHyperException "Field 'autfilt' must contain a string")

        BaitJarPath =
            (JSON.tryLookup "bait" x)
            |> Option.map (fun y ->
                y
                |> JSON.tryGetString
                |> Option.defaultWith (fun _ -> raise <| AutoHyperException "Field 'bait' must contain a string")
            )

        RabitJarPath =
            (JSON.tryLookup "rabit" x)
            |> Option.map (fun y ->
                y
                |> JSON.tryGetString
                |> Option.defaultWith (fun _ -> raise <| AutoHyperException "Field 'rabit' must contain a string")
            )

        ForkliftJarPath =
            (JSON.tryLookup "forklift" x)
            |> Option.map (fun y ->
                y
                |> JSON.tryGetString
                |> Option.defaultWith (fun _ -> raise <| AutoHyperException "Field 'forklift' must contain a string")
            )

      }

let getSolverConfiguration () =
    // By convention the paths.json file is located in the same directory as the executable
    let configPath =
        System.IO.Path.Join [|
            System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location)
            "paths.json"
        |]

    // Check if the path to the config file exists
    if System.IO.FileInfo(configPath).Exists |> not then
        raise
        <| AutoHyperException "The paths.json file does not exist in the same directory as the executable"

    // Parse the config File
    let configContent =
        try
            File.ReadAllText configPath
        with _ ->
            raise <| AutoHyperException "Could not open paths.json file"

    let solverConfig = parseSolverConfigurationContent configContent

    if System.IO.FileInfo(solverConfig.AutfiltPath).Exists |> not then 
        raise <| AutoHyperException "The given path to the spot's autfilt does not exist"

    if System.IO.FileInfo(solverConfig.Ltl2tgbaPath).Exists |> not then 
        raise <| AutoHyperException "The given path to the spot's ltl2tgba does not exist"

    solverConfig
