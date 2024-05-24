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

module AtomExpression

open Util

type AtomVariableType =
    | Int
    | Bool

module AtomVariableType =

    let print t =
        match t with
        | Int -> "int"
        | Bool -> "bool"

type AtomVariableValue =
    | BoolValue of bool
    | IntValue of int

module AtomVariableValue =

    let print v =
        match v with
        | BoolValue b -> string b
        | IntValue x -> string x


type AtomOperator =
    | AND
    | OR
    | IMPLIES
    | EQUIV
    | NOT
    | EQ
    | LT
    | GT
    | LE
    | GE
    | ADD
    | SUB
    | MUL

    | MINUS

module AtomOperator =
    let print (opp) =
        match opp with
        | AND -> "&"
        | OR -> "|"
        | IMPLIES -> "->"
        | EQUIV -> "<->"
        | NOT -> "!"
        | EQ -> "="
        | LT -> "<"
        | GT -> ">"
        | LE -> "<="
        | GE -> ">="
        | ADD -> "+"
        | SUB -> "-"
        | MUL -> "*"
        | MINUS -> "-"

    let inferType (opp) (tl : list<AtomVariableType>) = 
        match opp with 
        | AND | OR -> 
            if List.forall ((=) Bool) tl then 
                Some Bool
            else 
                None
        | IMPLIES | EQUIV -> 
            if List.forall ((=) Bool) tl && List.length tl = 2 then 
                Some Bool
            else 
                None
        | NOT -> 
            if List.forall ((=) Bool) tl && List.length tl = 1 then 
                Some Bool
            else 
                None
        | EQ -> 
            if ((List.forall ((=) Int) tl) || (List.forall ((=) Bool) tl)) && List.length tl = 2 then 
                Some Bool
            else 
                None
         | LT | GT | LE | GE -> 
            if (List.forall ((=) Int) tl) && List.length tl = 2 then 
                Some Bool
            else 
                None
        | ADD | MUL -> 
            if List.forall ((=) Int) tl then 
                Some Int
            else 
                None
        | SUB  -> 
            if List.forall ((=) Int) tl && List.length tl = 2  then 
                Some Int
            else 
                None
        | MINUS  -> 
            if List.forall ((=) Int) tl && List.length tl = 1  then 
                Some Int
            else 
                None


type AtomExpression<'T> =
    | Variable of 'T
    | BoolConstant of bool
    | IntConstant of int
    | App of AtomOperator * list<AtomExpression<'T>>


module AtomExpression =

    let rec allVars (e : AtomExpression<'T>) =
        match e with
        | Variable s -> Set.singleton s
        | BoolConstant _
        | IntConstant _ -> Set.empty
        | App(_, l) -> l |> List.map allVars |> Set.unionMany

    let rec map (m : 'T -> 'a) (e : AtomExpression<'T>) =
        match e with
        | Variable s -> Variable(m s)
        | IntConstant c -> IntConstant c
        | BoolConstant c -> BoolConstant c
        | App(n, l) -> App(n, List.map (map m) l)

    let rec bind (m : 'T -> AtomExpression<'A>) (e : AtomExpression<'T>) =
        match e with
        | Variable s -> m s
        | IntConstant c -> IntConstant c
        | BoolConstant c -> BoolConstant c
        | App(n, l) -> App(n, List.map (bind m) l)

    let simplify e = e

    let rec inferType (env : 'T -> AtomVariableType) (e : AtomExpression<'T>) = 
        match e with
        | Variable s -> Some(env s)
        | IntConstant _ -> Some Int
        | BoolConstant _ -> Some Bool
        | App(opp, l) -> 
            let tl = l |> List.map (inferType env)
            if List.exists Option.isNone tl then 
                None 
            else 
                AtomOperator.inferType opp (List.map Option.get tl)
            

    let rec print (varStringer : 'T -> string) (e : AtomExpression<'T>) =
        match e with
        | Variable s -> varStringer s
        | BoolConstant b -> "(" + string (b) + ")"
        | IntConstant i -> "(" + string (i) + ")"
        | App(opp, l) ->
            l
            |> List.map (print varStringer)
            |> String.concat " "
            |> fun x -> "(" + AtomOperator.print opp + " " + x + ")"



module Parser =
    open FParsec


    let private reservedWords =
        [

        ]

    /// Parses any possible symbol as defined by the SMTLIB standard
    let variableParser : Parser<string, unit> =
        let specialSymbolParser =
            choice
                [
                    pchar '~'
                    pchar '!'
                    pchar '@'
                    pchar '%'
                    pchar '^'
                    pchar '&'
                    pchar '*'
                    pchar '_'
                    pchar '-'
                    pchar '+'
                    pchar '='
                    pchar '<'
                    pchar '>'
                    pchar '.'
                    pchar '?'
                    pchar '/'
                ]

        let simpleSymbolParser =
            pipe2
                (letter <|> specialSymbolParser)
                (many (letter <|> digit <|> specialSymbolParser))
                (fun x y -> x :: y |> List.toArray |> string)

        let escapedStringParser =
            pipe3
                (pchar '|')
                (many (satisfy (fun c -> c <> '\\' && c <> '|')))
                (pchar '|')
                // We ignore the |s
                (fun _ x _ -> x |> List.toArray |> string)

        attempt (
            escapedStringParser <|> simpleSymbolParser
            >>= fun x -> if List.contains x reservedWords then fail "" else preturn x
        )

    let private operatorParser =
        choice
            [
                stringReturn "+" ADD
                stringReturn "-" SUB
                stringReturn "*" MUL
                stringReturn "and" AND
                stringReturn "or" OR

                stringReturn "=" EQ

                stringReturn "<=" LE
                stringReturn ">=" GE
                stringReturn "<" LT
                stringReturn ">" GT
            ]

    let atomExpressionParser (varParser : Parser<'T, unit>) =
        let atomExpressionParser, atomExpressionParserRef = createParserForwardedToRef ()

        let variableParser = varParser |>> Variable

        let constantParser =
            let intConstParser = pint32 |>> IntConstant

            let boolConstParser =
                stringReturn "true" (BoolConstant true)
                <|> stringReturn "false" (BoolConstant false)

            choice [ intConstParser; boolConstParser ]

        let appParser =
            pipe3
                (skipChar '(' >>. spaces >>. operatorParser .>> spaces)
                (many (atomExpressionParser .>> spaces) .>> spaces)
                (skipChar ')')
                (fun f l _ -> App(f, l))

        do atomExpressionParserRef.Value <- spaces >>. choice [ constantParser; appParser; variableParser ] .>> spaces

        atomExpressionParser

    let infixAtomExpressionParser (varParser : Parser<'T, unit>) =
        let atomExpressionParser, atomExpressionParserRef = createParserForwardedToRef ()

        let variableParser = varParser |>> Variable

        let constantParser =
            let intConstParser = pint32 |>> IntConstant

            let boolConstParser =
                stringReturn "true" (BoolConstant true)
                <|> stringReturn "false" (BoolConstant false)

            choice [ intConstParser; boolConstParser ]

        let parParser = skipString "(" >>. atomExpressionParser .>> skipChar ')'

        let opp : OperatorPrecedenceParser<AtomExpression<'T>, unit, unit> =
            new OperatorPrecedenceParser<AtomExpression<'T>, unit, unit>()

        let addInfixOperator string precedence associativity f =
            opp.AddOperator(InfixOperator(string, spaces, precedence, associativity, f))

        let addPrefixOperator string precedence associativity f =
            opp.AddOperator(PrefixOperator(string, spaces, precedence, associativity, f))

        addInfixOperator "*" 95 Associativity.Left (fun e1 e2 -> App(MUL, [ e1; e2 ]))

        addInfixOperator "+" 90 Associativity.Left (fun e1 e2 -> App(ADD, [ e1; e2 ]))
        addInfixOperator "-" 80 Associativity.Left (fun e1 e2 -> App(SUB, [ e1; e2 ]))
        addPrefixOperator "-" 100 true (fun x -> App(MINUS, [ x ]))

        addInfixOperator "==" 70 Associativity.Left (fun e1 e2 -> App(EQ, [ e1; e2 ]))
        addInfixOperator "!=" 70 Associativity.Left (fun e1 e2 -> App(NOT, [ App(EQ, [ e1; e2 ]) ]))
        addInfixOperator "<=" 70 Associativity.Left (fun e1 e2 -> App(LE, [ e1; e2 ]))
        addInfixOperator ">=" 70 Associativity.Left (fun e1 e2 -> App(GE, [ e1; e2 ]))
        addInfixOperator "<" 70 Associativity.Left (fun e1 e2 -> App(LT, [ e1; e2 ]))
        addInfixOperator ">" 70 Associativity.Left (fun e1 e2 -> App(GT, [ e1; e2 ]))

        addInfixOperator "&&" 50 Associativity.Left (fun e1 e2 -> App(AND, [ e1; e2 ]))

        addInfixOperator "||" 40 Associativity.Left (fun e1 e2 -> App(OR, [ e1; e2 ]))
        addPrefixOperator "!" 60 true (fun x -> App(NOT, [ x ]))
        addInfixOperator "=>" 30 Associativity.Left (fun e1 e2 -> App(IMPLIES, [ e1; e2 ]))


        let basicParser =
            spaces >>. choice [ constantParser; (attempt variableParser); parParser ]
            .>> spaces


        opp.TermParser <- basicParser

        do atomExpressionParserRef.Value <- opp.ExpressionParser

        atomExpressionParser

    let parseAtomExpression s =
        let parser = spaces >>. atomExpressionParser variableParser .>> spaces .>> eof
        let res = run parser s

        match res with
        | Success(res, _, _) -> Result.Ok res
        | Failure(err, _, _) -> Result.Error err
