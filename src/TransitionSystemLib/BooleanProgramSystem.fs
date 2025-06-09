module TransitionSystemLib.BooleanProgramSystem

open System
open System.Collections.Generic

open TransitionSystem

exception SystemConstructionException of String
exception private NotWellFormedException of String
exception private BitwidthCheckingException of String

type Var = String

type ProgramExpression =
    | True
    | False
    | Variable of Var
    | And of ProgramExpression * ProgramExpression
    | Or of ProgramExpression * ProgramExpression
    | Not of ProgramExpression
    | Indexing of ProgramExpression * int * int
    | Concat of ProgramExpression * ProgramExpression
    | Duplicate of ProgramExpression * int

module ProgramExpression =

    let rec usedVars (e : ProgramExpression) =
        match e with
        | True
        | False -> Set.empty
        | Variable x -> Set.singleton x
        | And(e1, e2)
        | Or(e1, e2)
        | Concat(e1, e2) -> Set.union (usedVars e1) (usedVars e2)
        | Not e
        | Indexing(e, _, _)
        | Duplicate(e, _) -> usedVars e

    let rec print (e : ProgramExpression) =
        match e with
        | True -> "true"
        | False -> "false"
        | Variable x -> x
        | And(e1, e2) -> "(" + print e1 + "&" + print e2 + ")"
        | Or(e1, e2) -> "(" + print e1 + "|" + print e2 + ")"
        | Not e -> "(!" + print e + ")"
        | Indexing(e, l, u) -> "(" + print e + "[" + string l + "," + string u + "])"
        | Concat(e1, e2) -> "(" + print e1 + "@" + print e2 + ")"
        | Duplicate(e, n) -> "(" + string n + "*" + print e + ")"

    let rec eval (A : Map<Var, list<bool>>) (e : ProgramExpression) =
        match e with
        | True -> [ true ]
        | False -> [ false ]
        | Variable x -> A.[x]
        | And(e1, e2) -> List.zip (eval A e1) (eval A e2) |> List.map (fun (x, y) -> x && y)
        | Or(e1, e2) -> List.zip (eval A e1) (eval A e2) |> List.map (fun (x, y) -> x || y)
        | Not e -> eval A e |> List.map not
        | Indexing(e, l, u) ->
            let r = eval A e
            let range = [ l..u ]

            if range |> List.forall (fun x -> 0 <= x && x < List.length r) |> not then
                raise
                <| SystemConstructionException
                    $"Expression %s{print e} evalutes to a vector of length %i{List.length r} of which we cannot take the range [%i{l}, %i{u}]"
            else
                r.[l..u]
        | Concat(e1, e2) -> List.append (eval A e1) (eval A e2)
        | Duplicate(e, n) ->
            let t = eval A e
            List.init n (fun _ -> t) |> List.concat

    let rec inferBitWidth (env : Var -> int) (e : ProgramExpression) =
        match e with
        | True -> 1
        | False -> 1
        | Variable x -> env x
        | And(e1, e2) ->
            let r1 = inferBitWidth env e1
            let r2 = inferBitWidth env e2

            if r1 <> r2 then
                raise
                <| BitwidthCheckingException
                    $"Expressions %s{print e1} and %s{print e2} have bitwidths %i{r1} and %i{r2} and thus cannot be compared with an 'and'"
            else
                r1
        | Or(e1, e2) ->
            let r1 = inferBitWidth env e1
            let r2 = inferBitWidth env e2

            if r1 <> r2 then
                raise
                <| BitwidthCheckingException
                    $"Expressions %s{print e1} and %s{print e2} have bitwidths %i{r1} and %i{r2} and thus cannot be compared with an 'or'"
            else
                r1
        | Not e -> inferBitWidth env e
        | Indexing(e, l, u) ->
            let r = inferBitWidth env e
            let range = [ l..u ]

            if range |> List.forall (fun x -> 0 <= x && x < r) |> not then
                raise
                <| SystemConstructionException
                    $"Expression %s{print e} has bitwidths %i{r} so we cannot take the range [%i{l}, %i{u}]"
            else
                List.length range
        | Concat(e1, e2) ->
            let r1 = inferBitWidth env e1
            let r2 = inferBitWidth env e2
            r1 + r2
        | Duplicate(e, n) ->
            let r = inferBitWidth env e
            n * r

type ProgramStatement =
    | Terminated
    | Skip
    | Assignment of Var * ProgramExpression
    | If of ProgramExpression * ProgramStatement * ProgramStatement
    | Nondet of ProgramStatement * ProgramStatement
    | NondetAssignment of Var
    | Seq of list<ProgramStatement>
    | While of ProgramExpression * ProgramStatement

module ProgramStatement =

    let rec usedVars (s : ProgramStatement) =
        match s with
        | Terminated
        | Skip -> Set.empty
        | Assignment(v, e) -> Set.add v (ProgramExpression.usedVars e)
        | If(e, s1, s2) -> [ ProgramExpression.usedVars e; usedVars s1; usedVars s2 ] |> Set.unionMany
        | Nondet(s1, s2) -> Set.union (usedVars s1) (usedVars s2)
        | NondetAssignment x -> Set.singleton x
        | Seq slist -> slist |> List.map usedVars |> Set.unionMany
        | While(e, s) -> Set.union (ProgramExpression.usedVars e) (usedVars s)


    let rec oneStep (A : Map<Var, list<bool>>) (s : ProgramStatement) =
        match s with
        | Terminated -> Seq.singleton (Terminated, A)
        | Skip -> Seq.singleton (Terminated, A)
        | Assignment(v, e) ->
            let newVal = ProgramExpression.eval A e
            let newAssignment = Map.add v newVal A
            Seq.singleton (Terminated, newAssignment)
        | If(e, s1, s2) ->
            let res = ProgramExpression.eval A e

            if res.[0] then
                Seq.singleton (s1, A)
            else
                Seq.singleton (s2, A)
        | Nondet(s1, s2) ->
            seq {
                (s1, A)
                (s2, A)
            }
        | NondetAssignment v ->
            let width = A.[v].Length

            seq {
                for b in Util.computeBooleanPowerSet width do
                    (Terminated, Map.add v b A)
            }
        | Seq slist ->
            match slist with
            | [] -> Seq.singleton (Terminated, A)
            | [ x ] -> oneStep A x
            | x :: xs ->
                oneStep A x
                |> Seq.map (fun (s, A') ->
                    match s with
                    | Terminated -> (Seq xs, A')
                    | t -> (Seq(t :: xs), A')
                )
        | While(e, s) ->
            let res = ProgramExpression.eval A e

            if res.[0] then
                Seq.singleton (
                    Seq[s
                        While(e, s)],
                    A
                )
            else
                Seq.singleton (Terminated, A)

type BooleanProgram =
    {
        DomainMap : Map<Var, int>
        Statement : ProgramStatement
    }

module BooleanProgram =
    let findError (p : BooleanProgram) =
        try
            let usedVars = ProgramStatement.usedVars p.Statement

            usedVars
            |> Set.iter (fun x ->
                if p.DomainMap.ContainsKey x |> not then
                    raise
                    <| NotWellFormedException $"Variable %s{x} is used the program but not defined in the domain."
            )

            let rec findErrorRec (dom : Var -> int) (s : ProgramStatement) =
                match s with
                | Terminated -> ()
                | Skip -> ()
                | Assignment(v, e) ->
                    let r = ProgramExpression.inferBitWidth dom e

                    if r <> dom v then
                        raise
                        <| NotWellFormedException
                            $"Variable %s{v} has width %i{dom v} but is assigned expression %s{ProgramExpression.print e} with width %i{r}"
                | If(e, s1, s2) ->
                    let r = ProgramExpression.inferBitWidth dom e

                    if r <> 1 then
                        raise
                        <| NotWellFormedException
                            $"Expression %s{ProgramExpression.print e} has width %i{r} but is used in a conditional and should have width 1"

                    findErrorRec dom s1
                    findErrorRec dom s2

                | Nondet(s1, s2) ->
                    findErrorRec dom s1
                    findErrorRec dom s2
                | NondetAssignment _ -> ()
                | Seq slist -> slist |> List.iter (findErrorRec dom)
                | While(e, s) ->
                    let r = ProgramExpression.inferBitWidth dom e

                    if r <> 1 then
                        raise
                        <| NotWellFormedException
                            $"Expression %s{ProgramExpression.print e} has width %i{r} but is used as a loop guard and should have width 1"

                    findErrorRec dom s

            findErrorRec (fun x -> p.DomainMap.[x]) p.Statement

            None
        with
        | NotWellFormedException msg -> Some msg
        | BitwidthCheckingException msg -> Some msg

    let convertBooleanProgramToTransitionSystem (P : BooleanProgram) (relevantAps : list<Var * int>) =
        let initialState =
            (P.Statement, Map.map (fun _ x -> List.init x (fun _ -> false)) P.DomainMap)

        let allStates = new HashSet<_>()
        let queue = new Queue<_>()
        queue.Enqueue initialState
        allStates.Add initialState |> ignore

        let edgeDict = new Dictionary<_, _>()
        let variableEvalDict = new Dictionary<_, _>()

        while queue.Count <> 0 do
            let s = queue.Dequeue()
            let p, A = s

            let sucs = ProgramStatement.oneStep A p |> set

            let variableEval =
                relevantAps
                |> List.map (fun (v, j) -> (v, j), (BoolValue(A.[v].[j])))
                |> Map.ofList

            for s' in sucs do
                if allStates.Contains s' |> not then
                    queue.Enqueue s'
                    allStates.Add s' |> ignore

            edgeDict.Add(s, sucs)
            variableEvalDict.Add(s, variableEval)


        let renamingDict = allStates |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq


        let statePrinter =
            renamingDict
            |> Map.toSeq
            |> Seq.map (fun ((_, s), i) ->

                let printedString =
                    s
                    |> Map.toSeq
                    |> Seq.map (fun (var, v) ->
                        var + ":" + (v |> List.map string |> String.concat ";" |> (fun x -> $"[{x}]"))
                    )
                    |> String.concat ", "
                    |> fun x -> "{" + x + "}"

                i, printedString
            )
            |> Map.ofSeq

        let ts =
            {
                States = allStates |> Seq.map (fun x -> renamingDict[x]) |> set
                InitialStates = renamingDict[initialState] |> Set.singleton
                AcceptingStates = None
                VariableType = relevantAps |> List.map (fun x -> x, Bool) |> Map.ofList
                Edges =
                    edgeDict
                    |> Seq.map (fun x -> x.Key, x.Value)
                    |> Seq.map (fun (k, v) -> renamingDict[k], Set.map (fun x -> renamingDict[x]) v)
                    |> Map.ofSeq
                VariableEval =
                    variableEvalDict
                    |> Seq.map (fun x -> x.Key, x.Value)
                    |> Seq.map (fun (k, v) -> renamingDict[k], v)
                    |> Map.ofSeq
            }

        {
            TransitionSystemWithPrinter.TransitionSystem = ts
            Printer = statePrinter
        }


module Parser =
    open FParsec

    let private commentParser = (skipString "--" .>> restOfLine false)

    let private ws = spaces .>> sepEndBy commentParser spaces

    let private keywords = [ "if"; "else"; "while"; "true"; "false" ]

    let variableParser =
        attempt (
            (letter <|> pchar '_') .>>. manyChars (letter <|> digit <|> pchar '_')
            >>= fun (x, y) ->
                (let s = string (x) + y
                 if List.contains s keywords then fail "" else preturn s)
        )

    let programExpressionParser =
        let expParser, expParserRef = createParserForwardedToRef ()

        let trueParser = stringReturn "true" ProgramExpression.True

        let falseParser = stringReturn "false" ProgramExpression.False

        let variableParser = variableParser |>> Variable

        let parParser = skipChar '(' >>. ws >>. expParser .>> ws .>> skipChar ')'

        let multParser =
            pipe2 (pint32 .>> ws .>> skipChar '*' .>> ws) expParser (fun n e -> ProgramExpression.Duplicate(e, n))


        let basicParser =
            ws >>. choice [ trueParser; falseParser; parParser; multParser; variableParser ]
            .>> ws

        let oppParser = new OperatorPrecedenceParser<ProgramExpression, unit, unit>()

        let addInfixOperator string precedence associativity f =
            oppParser.AddOperator(InfixOperator(string, ws, precedence, associativity, f))

        let addPrefixOperator string precedence associativity f =
            oppParser.AddOperator(PrefixOperator(string, ws, precedence, associativity, f))

        do
            oppParser.TermParser <- basicParser
            addPrefixOperator "!" 30 true (fun x -> ProgramExpression.Not x)
            addInfixOperator "&" 20 Associativity.Left (fun x y -> ProgramExpression.And(x, y))
            addInfixOperator "|" 10 Associativity.Left (fun x y -> ProgramExpression.Or(x, y))
            addInfixOperator "@" 5 Associativity.None (fun x y -> ProgramExpression.Concat(x, y))

        do
            expParserRef.Value <-
                oppParser.ExpressionParser
                >>= (fun e ->
                    attempt (
                        skipChar '[' >>. ws >>. tuple2 (pint32 .>> ws .>> skipChar ',' .>> ws) (pint32)
                        .>> ws
                        .>> skipChar ']'
                        |>> (fun (l, u) -> Indexing(e, l, u))
                    )
                    <|> attempt (
                        skipChar '[' >>. ws >>. pint32 .>> ws .>> skipChar ']'
                        |>> (fun i -> Indexing(e, i, i))
                    )
                    <|> preturn e
                )

        expParser

    let statementParser =
        let statementParser, statementParserRef = createParserForwardedToRef ()

        let assignmentParser =
            variableParser .>> ws
            >>= (fun v ->
                attempt (skipChar '=' >>. ws >>. skipChar '*' |>> (fun _ -> NondetAssignment v))
                <|> attempt (skipChar '=' >>. ws >>. programExpressionParser |>> (fun e -> Assignment(v, e)))
            )

        let ifParser =
            let elIfParser =
                pipe2
                    (skipString "elif" >>. ws >>. programExpressionParser .>> ws)
                    (skipChar '{' >>. statementParser .>> skipChar '}' .>> ws)
                    (fun g s -> (g, s))

            let elseParser =
                (skipString "else" >>. ws >>. skipChar '{' >>. ws >>. statementParser
                 .>> skipChar '}')

            pipe4
                (attempt (skipString "if" >>. ws >>. programExpressionParser .>> ws))
                (skipChar '{' >>. statementParser .>> skipChar '}' .>> ws)
                (many (elIfParser .>> ws))
                (opt elseParser)
                (fun g m eif el ->
                    let el = Option.defaultValue Skip el
                    let a = (eif, el) ||> List.foldBack (fun (g, s) x -> If(g, s, x))
                    If(g, m, a)
                )

        let nondetParser =
            pipe3
                (attempt (skipString "if" >>. ws >>. skipChar '*' .>> ws))
                (skipChar '{' >>. statementParser
                 .>> skipChar '}'
                 .>> ws
                 .>> skipString "else"
                 .>> ws)
                (skipChar '{' >>. statementParser .>> skipChar '}')
                (fun _ x y -> Nondet(x, y))

        let skipParser = stringReturn "SKIP" Skip

        let whileParser =
            pipe2
                (skipString "while" >>. ws >>. programExpressionParser .>> ws)
                (skipChar '{' >>. statementParser .>> skipChar '}')
                (fun g p -> While(g, p))

        let parParser = skipChar '{' >>. statementParser .>> skipChar '}'

        let basicBlockParser =
            ws
            >>. choice
                    [
                        skipParser .>> ws .>> skipChar ';'
                        whileParser
                        ifParser
                        nondetParser
                        assignmentParser .>> ws .>> skipChar ';'
                        parParser
                    ]
            .>> ws

        do
            statementParserRef.Value <-
                many1 basicBlockParser
                |>> function
                    | [ x ] -> x
                    | xs -> Seq xs

        statementParser

    let domainSizeParser =
        let asignmentParser =
            tuple2 (variableParser .>> ws .>> skipChar ':' .>> ws) (pint32 .>> ws .>> skipChar ';')
            |> attempt

        many (asignmentParser .>> ws) |>> Map.ofList

    let programParser =
        pipe2
            (domainSizeParser .>> ws)
            statementParser
            (fun x y ->
                {
                    BooleanProgram.DomainMap = x
                    Statement = y
                }
            )

    let parseBooleanProgram (s : String) =
        let full = programParser .>> ws .>> eof

        let res = run full s

        match res with
        | Success(res, _, _) -> Result.Ok res
        | Failure(err, _, _) -> Result.Error err
