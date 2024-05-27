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

module HyperQPTL

open FsOmegaLib.LTL

open AtomExpression

type TraceVariable = string
type PropVariable = string

type QuantifierType =
    | FORALL
    | EXISTS

module QuantifierType =
    let flip =
        fun q ->
            match q with
            | FORALL -> EXISTS
            | EXISTS -> FORALL

    let print =
        fun q ->
            match q with
            | FORALL -> "forall"
            | EXISTS -> "exists"


type HyperQPTLQuantifier =
    | TraceQuantifier of QuantifierType * PropVariable
    | PropQuantifier of QuantifierType * PropVariable

type ExpressionAtom<'L> =
    | TraceAtom of 'L * TraceVariable
    | PropAtom of PropVariable

module ExpressionAtom = 
    let print (varStringer : 'L -> string) atom = 
        match atom with 
        | TraceAtom (var, pi) -> "\"" + varStringer var + "\"" + "_" + pi
        | PropAtom q -> q

type HyperQPTL<'L when 'L : comparison> =
    {
        QuantifierPrefix : list<HyperQPTLQuantifier>
        LTLMatrix : LTL<AtomExpression<ExpressionAtom<'L>>>
    }

module HyperQPTL =
    let quantifiedTraceVariables (formula : HyperQPTL<'L>) : list<TraceVariable> =
        formula.QuantifierPrefix
        |> List.choose (fun x ->
            match x with
            | TraceQuantifier(_, pi) -> Some pi
            | _ -> None
        )

    let quantifiedPropVariables (formula : HyperQPTL<'L>) : list<PropVariable>  =
        formula.QuantifierPrefix
        |> List.choose (fun x ->
            match x with
            | PropQuantifier(_, p) -> Some p
            | _ -> None
        )


    let map f (formula : HyperQPTL<'L>) =
        {
            QuantifierPrefix = formula.QuantifierPrefix
            LTLMatrix =
                formula.LTLMatrix
                |> LTL.map (
                    AtomExpression.map (
                        function
                        | PropAtom q -> PropAtom q
                        | TraceAtom(x, n) -> TraceAtom(f x, n)
                    )
                )
        }

    exception private FoundError of string

    let findError (formula : HyperQPTL<'L>) =
        let propVars = quantifiedPropVariables formula

        let traceVars = quantifiedTraceVariables formula

        try
            propVars
            |> List.groupBy id
            |> List.iter (fun (p, l) ->
                if List.length l > 1 then
                    raise <| FoundError $"Propositional variable {p} is used more than once"
            )

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
                |> Set.iter (fun y ->
                    match y with
                    | PropAtom q ->
                        if List.contains q propVars |> not then
                            raise
                            <| FoundError $"Propositional variable '{q}' is used but not defined in the prefix"

                    | TraceAtom(_, pi) ->
                        if List.contains pi traceVars |> not then
                            raise
                            <| FoundError $"Trace variable '{pi}' is used but not defined in the prefix"
                )
            )

            None

        with FoundError msg ->
            Some msg

    let print (varNames : 'L -> string) (formula : HyperQPTL<'L>) =
        let prefixString =
            formula.QuantifierPrefix
            |> List.map (
                function
                | TraceQuantifier(FORALL, pi) -> "forall " + pi + ". "
                | TraceQuantifier(EXISTS, pi) -> "exists " + pi + ". "
                | PropQuantifier(FORALL, p) -> "A " + p + ". "
                | PropQuantifier(EXISTS, p) -> "E " + p + ". "
            )
            |> String.concat " "

        let varStringer x =
            match x with
            | TraceAtom(x, pi) -> "{" + varNames x + "}_" + pi
            | PropAtom p -> string p

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

module Parser =
    open FParsec

    let private keywords = [ "X"; "G"; "F"; "U"; "W"; "R" ]

    let traceVariableParser =
        attempt (
            pipe2 letter (manyChars (letter <|> digit)) (fun x y -> string (x) + y)
            >>= fun s -> if List.contains s keywords then fail "" else preturn s
        )

    let propVariableParser = traceVariableParser

    let ws = spaces

    let prefixParser =
        let existsTraceParser =
            skipString "exists " >>. ws >>. traceVariableParser .>> ws .>> pchar '.'
            |>> fun pi -> TraceQuantifier(EXISTS, pi)

        let forallTraceParser =
            skipString "forall " >>. ws >>. traceVariableParser .>> ws .>> pchar '.'
            |>> fun pi -> TraceQuantifier(FORALL, pi)

        let existsPropParser =
            skipString "E " >>. ws >>. propVariableParser .>> ws .>> pchar '.'
            |>> fun p -> PropQuantifier(EXISTS, p)

        let forallPropParser =
            skipString "A " >>. ws >>. propVariableParser .>> ws .>> pchar '.'
            |>> fun p -> PropQuantifier(FORALL, p)

        many1 (
            choice [ existsTraceParser; forallTraceParser; existsPropParser; forallPropParser ]
            .>> ws
        )


    let ltlAtomParser systemVariableParser =
        let expressionAtomParser =
            attempt (
                pipe2
                    (between (skipChar '"' .>> ws) (skipChar '"') (systemVariableParser .>> ws))
                    (pchar '_' >>. traceVariableParser)
                    (fun x pi -> TraceAtom(x, pi))
            )
            <|> (propVariableParser |>> PropAtom)

        let fullExpressionAtom =
            between
                (skipChar '{' .>> ws)
                (skipChar '}')
                (AtomExpression.Parser.infixAtomExpressionParser expressionAtomParser .>> ws)

        let singleVariableAtom =
            pipe2
                (between (skipChar '"' .>> ws) (skipChar '"') (systemVariableParser .>> ws))
                (pchar '_' >>. traceVariableParser)
                (fun x pi -> TraceAtom(x, pi))
            |>> AtomExpression.Variable

        choice [ fullExpressionAtom; singleVariableAtom ]


    let hyperQPTLParser (systemVariableParser : Parser<'T, unit>) =
        pipe2
            prefixParser
            (FsOmegaLib.LTL.Parser.ltlParser (ltlAtomParser systemVariableParser))
            (fun x y ->
                {
                    HyperQPTL.QuantifierPrefix = x
                    LTLMatrix = y
                }
            )

    let parseHyperQPTL (systemVariableParser : Parser<'T, unit>) s =
        let full = hyperQPTLParser systemVariableParser .>> spaces .>> eof
        let res = run full s

        match res with
        | Success(res, _, _) -> Result.Ok res
        | Failure(err, _, _) -> Result.Error err

    let parseHyperQPTLSymbolicSystem s =
        parseHyperQPTL (TransitionSystemLib.SymbolicSystem.Parser.identifierParser) s

    let parseHyperQPTLExplicitSystem s =
        parseHyperQPTL (TransitionSystemLib.TransitionSystem.Parser.variableParser) s

    let parseHyperQPTLBooleanProgram s =
        let varParser = 
            tuple2 
                (TransitionSystemLib.BooleanProgramSystem.Parser.variableParser .>> spaces .>> skipChar ',')
                (pint32 .>> spaces)

        parseHyperQPTL varParser s
        

    