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

module HyperLTL

open FsOmegaLib.LTL

open AtomExpression
open HyperQPTL

type TraceVariable = string

type HyperLTL<'L when 'L : comparison> =
    {
        QuantifierPrefix : list<QuantifierType * TraceVariable>
        LTLMatrix : LTL<AtomExpression<'L * TraceVariable>>
    }

module HyperLTL =
    let quantifiedTraceVariables (formula : HyperLTL<'L>) =
        formula.QuantifierPrefix |> List.map snd

    let map f (formula : HyperLTL<'L>) =
        {
            QuantifierPrefix = formula.QuantifierPrefix
            LTLMatrix = formula.LTLMatrix |> LTL.map (AtomExpression.map (fun (x, pi) -> f x, pi))
        }

    exception private FoundError of string

    let findError (formula : HyperLTL<'L>) =
        let traceVars = quantifiedTraceVariables formula

        try
            traceVars
            |> List.groupBy id
            |> List.iter (fun (pi, l) ->
                if List.length l > 1 then
                    raise <| FoundError $"Trace variable {pi} is used more than once"
            )

            LTL.allAtoms formula.LTLMatrix
            |> Set.iter (fun x ->
                x
                |> AtomExpression.allVars
                |> Set.iter (fun (_, pi) ->
                    if List.contains pi traceVars |> not then
                        raise
                        <| FoundError $"Trace variable '{pi}' is used but not defined in the prefix"
                )
            )

            None

        with FoundError msg ->
            Some msg

    let print (varNames : 'L -> string) (formula : HyperLTL<'L>) =
        let prefixString =
            formula.QuantifierPrefix
            |> List.map (fun (q, pi) -> 
                match q with
                | FORALL -> "forall " + pi + ". "
                | EXISTS -> "exists " + pi + ". "
            )
            |> String.concat " "

        let varStringer (x, pi) = "{" + varNames x + "}_" + pi

        let expressionStringer e =
            match e with
            | Variable x ->
                // Single variable, print directly with parenthesis
                varStringer x
            | _ -> "[" + AtomExpression.print varStringer e + "]"

        let ltlString = LTL.printInSpotFormat expressionStringer formula.LTLMatrix

        prefixString + " " + ltlString

(*
let extractBlocks (qf : list<TraceQuantifierType>) =
    let rec helper t count q =
        match q with
        | [] -> [ count ]
        | x :: xs ->
            if x = t then
                helper t (count + 1) xs
            else
                count :: helper x 1 xs

    helper qf.[0] 0 qf
*)
