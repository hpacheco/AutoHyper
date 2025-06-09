module TransitionSystemLib.Util

open System.Collections.Generic



/// Given a number n, computes all lists of booleans of length n
let rec computeBooleanPowerSet n =
    if n = 0 then
        Seq.singleton []
    else
        let r = computeBooleanPowerSet (n - 1)
        Seq.append (Seq.map (fun x -> true :: x) r) (Seq.map (fun x -> false :: x) r)

let rec cartesianProduct (LL: list<seq<'a>>) =
    match LL with
    | [] -> Seq.singleton []
    | L :: Ls ->
        seq {
            for x in L do
                for xs in cartesianProduct Ls -> x :: xs
        }

let cartesianProductMap (m: Map<'A, Set<'B>>) =
    let keysAsList = Seq.toList m.Keys

    keysAsList
    |> Seq.toList
    |> List.map (fun x -> m.[x] |> seq)
    |> cartesianProduct
    |> Seq.map (fun x -> List.zip keysAsList x |> Map)


let dictToMap (d: Dictionary<'A, 'B>) =
    d |> Seq.map (fun x -> x.Key, x.Value) |> Map.ofSeq


module ParserUtil =

    open FParsec

    let escapedStringParser: Parser<string, unit> =
        let escapedCharParser: Parser<string, unit> =
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
