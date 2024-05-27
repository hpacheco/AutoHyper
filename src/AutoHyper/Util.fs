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

module Util

open System
open System.Collections.Generic

exception AutoHyperException of String

/// Given a number n, computes all lists of booleans of length n
let rec computeBooleanPowerSet n =
    if n = 0 then
        Seq.singleton []
    else
        let r = computeBooleanPowerSet (n - 1)
        Seq.append (Seq.map (fun x -> true :: x) r) (Seq.map (fun x -> false :: x) r)

/// Compute the cartesian product of a list of sets
let rec cartesianProduct (LL : list<seq<'a>>) =
    match LL with
    | [] -> Seq.singleton []
    | L :: Ls ->
        seq {
            for x in L do
                for xs in cartesianProduct Ls -> x :: xs
        }

/// Compute the powerset of a given set
let powerset (s : Set<'a>) =
    let asList = Set.toList s

    let rec computeFiniteChoices (A : list<'a>) =
        match A with
        | [] -> Seq.singleton Set.empty
        | x :: xs ->
            let r = computeFiniteChoices xs
            Seq.append r (Seq.map (fun y -> Set.add x y) r)

    computeFiniteChoices asList

/// Given a map 'A -> set<'B> compute all possible maps 'A -> 'B that are obtained by picking some element from that set for each key in 'A
let cartesianProductMap (m : Map<'A, Set<'B>>) =
    let keysAsList = Seq.toList m.Keys

    keysAsList
    |> Seq.toList
    |> List.map (fun x -> m.[x] |> seq)
    |> cartesianProduct
    |> Seq.map (fun x -> List.zip keysAsList x |> Map)

let dictToMap (d : Dictionary<'A, 'B>) =
    d |> Seq.map (fun x -> x.Key, x.Value) |> Map.ofSeq

/// Parser for variables used in HyperLTL specifications
module ParserUtil =
    open FParsec

    let escapedStringParser : Parser<string, unit> =
        let escapedCharParser : Parser<string, unit> =
            anyOf "\"\\/bfnrt"
            |>> fun x ->
                match x with
                | 'b' -> "\b"
                | 'f' -> "\u000C"
                | 'n' -> "\n"
                | 'r' -> "\r"
                | 't' -> "\t"
                | c -> string c

        between
            (pchar '"')
            (pchar '"')
            (stringsSepBy (manySatisfy (fun c -> c <> '"' && c <> '\\')) (pstring "\\" >>. escapedCharParser))




module SubprocessUtil =
    type SubprocessResult =
        {
            Stdout : String
            Stderr : String
            ExitCode : int
        }

    open System.Diagnostics

    let runProc filename args : seq<string> * seq<string> =
        let timer = Stopwatch.StartNew()

        let procStartInfo =
            ProcessStartInfo(
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                FileName = filename,
                Arguments = args
            )
        // match startDir with | Some d -> procStartInfo.WorkingDirectory <- d | _ -> ()

        let outputs = System.Collections.Generic.List<string>()
        let errors = System.Collections.Generic.List<string>()
        let outputHandler f (_sender : obj) (args : DataReceivedEventArgs) = f args.Data
        use p = new Process(StartInfo = procStartInfo)
        p.OutputDataReceived.AddHandler(DataReceivedEventHandler(outputHandler outputs.Add))
        p.ErrorDataReceived.AddHandler(DataReceivedEventHandler(outputHandler errors.Add))

        let started =
            try
                p.Start()
            with ex ->
                ex.Data.Add("filename", filename)
                reraise ()

        if not started then
            failwithf "Failed to start process %s" filename

        printfn "Started %s with pid %i" p.ProcessName p.Id
        p.BeginOutputReadLine()
        p.BeginErrorReadLine()
        p.WaitForExit()
        timer.Stop()
        printfn "Finished %s after %A milliseconds" filename timer.ElapsedMilliseconds

        let cleanOut l =
            l |> Seq.filter (fun o -> String.IsNullOrEmpty o |> not)

        cleanOut outputs, cleanOut errors

    let executeSubprocess (envVariables : Map<string, string>) (cmd : string) (arg : string) =
        let psi = System.Diagnostics.ProcessStartInfo(cmd, arg)

        psi.UseShellExecute <- false
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.CreateNoWindow <- true

        for (var, v) in Map.toSeq envVariables do
            psi.Environment.Add(var, v)

        let p = System.Diagnostics.Process.Start(psi)
        let output = System.Text.StringBuilder()
        let error = System.Text.StringBuilder()

        p.OutputDataReceived.Add(fun args -> output.Append(args.Data + "\n") |> ignore)
        p.ErrorDataReceived.Add(fun args -> error.Append(args.Data + "\n") |> ignore)
        p.BeginErrorReadLine()
        p.BeginOutputReadLine()
        p.WaitForExit()

        {
            SubprocessResult.Stdout = output.ToString().Trim()
            Stderr = error.ToString().Trim()
            ExitCode = p.ExitCode
        }
