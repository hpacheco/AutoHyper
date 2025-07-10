module TransitionSystemLib.TransitionSystem

open System
open System.IO

type VariableType =
    | Int
    | Bool

module VariableType =

    let print t =
        match t with
        | Int -> "Int"
        | Bool -> "Bool"

type VariableValue =
    | BoolValue of bool
    | IntValue of int

module VariableValue =

    let print v =
        match v with
        | BoolValue b -> string b
        | IntValue x -> string x

type TransitionSystem<'L when 'L : comparison> =
    {
        States : Set<int>
        InitialStates : Set<int>
        AcceptingStates : Set<int> option
        VariableType : Map<'L, VariableType>
        Edges : Map<int, Set<int>>
        VariableEval : Map<int, Map<'L, VariableValue>>
    }

module TransitionSystem =

    let mapVariables (f : 'L -> 'U) (ts : TransitionSystem<'L>) =
        {
            States = ts.States
            InitialStates = ts.InitialStates
            AcceptingStates = ts.AcceptingStates
            VariableType = ts.VariableType |> Map.toSeq |> Seq.map (fun (k, v) -> f k, v) |> Map.ofSeq
            Edges = ts.Edges
            VariableEval =
                ts.VariableEval
                |> Map.map (fun _ m -> m |> Map.toSeq |> Seq.map (fun (k, v) -> f k, v) |> Map.ofSeq)
        }


    exception private FoundError of String

    let alignWithTypes (ts : TransitionSystem<'L>) =
        try
            {
                States = ts.States
                InitialStates = ts.InitialStates
                AcceptingStates = ts.AcceptingStates
                VariableType = ts.VariableType
                Edges = ts.Edges
                VariableEval =
                    ts.VariableEval
                    |> Map.map (fun s m ->
                        ts.VariableType
                        |> Map.map (fun x t ->
                            match t, Map.tryFind x m with
                            | Bool, None -> BoolValue false
                            | Int, None ->
                                raise
                                <| FoundError $"In state '{s}' no value for integer-valued variable '{x}' is given"
                            | Bool, Some(IntValue _) ->
                                raise
                                <| FoundError
                                    $"In state '{s}', variable '{x}' is assigned an integer, but assigned type 'Bool'"
                            | Int, Some(BoolValue _) ->
                                raise
                                <| FoundError
                                    $"In state '{s}', variable '{x}' is assigned a boolean, but assigned type 'Int'"
                            | _, Some v -> v
                        )

                    )
            }
            |> Result.Ok

        with FoundError err ->
            Result.Error err

    let findError (ts : TransitionSystem<'L>) =
        try
            ts.States
            |> Seq.iter (fun x ->
                if ts.Edges.ContainsKey x |> not then
                    raise <| FoundError $"No successor defined for state '{x}'"

                if ts.VariableEval.ContainsKey x |> not then
                    raise <| FoundError $"No variable evaluation defined for state '{x}'"

                ts.VariableEval.[x]
                |> Map.iter (fun y v ->

                    match Map.tryFind y ts.VariableType, v with
                    | None, _ ->
                        raise
                        <| FoundError $"In state '{x}', variable '{y}' is defined but not declared in the system"
                    | Some Int, IntValue _ -> ()
                    | Some Bool, BoolValue _ -> ()
                    | _ ->
                        raise
                        <| FoundError
                            $"In state '{x}', variable '{y}' is assigned a value that does not match its declared type"
                )
            )

            ts.InitialStates
            |> Seq.iter (fun s ->
                if ts.States.Contains s |> not then
                    raise
                    <| FoundError $"The initial state '{s}' is not contained in the set of all states"
            )
            
            match ts.AcceptingStates with
            | None -> ()
            | Some xs -> xs |> Seq.iter (fun s ->
                if ts.States.Contains s |> not then
                    raise
                    <| FoundError $"The initial state '{s}' is not contained in the set of all states"
            )

            ts.Edges
            |> Map.toSeq
            |> Seq.iter (fun (k, x) ->
                x
                |> Seq.iter (fun z ->
                    if ts.States.Contains z |> not then
                        raise
                        <| FoundError $"State '{z}' is a successor of states '{k}' but not defined as a state"
                )
            )

            None

        with FoundError msg ->
            Some msg


    let print (varStringer : 'L -> string) (ts : TransitionSystem<'L>) =
        let strWriter = new StringWriter()

        strWriter.Write("Variables: ")

        for (x, t) in Map.toSeq ts.VariableType do
            strWriter.Write("(" + "\"" + varStringer x + "\"" + " " + VariableType.print t + ") ")

        strWriter.Write('\n')

        strWriter.Write("Init: ")

        for s in ts.InitialStates do
            strWriter.Write(string (s) + " ")

        strWriter.Write('\n')

        match ts.AcceptingStates with
        | None -> ()
        | Some xs -> 
            strWriter.Write("Accepting: ")
            for s in xs do
                strWriter.Write(string (s) + " ")
                strWriter.Write('\n')

        strWriter.Write("--BODY--\n")

        for s in ts.States do
            let sucs = ts.Edges.[s]
            let variableEval = ts.VariableEval.[s]

            strWriter.Write("State: " + string s + " ")

            strWriter.Write("{")

            variableEval
            |> Map.iter (fun x v ->
                match v with
                | IntValue i -> strWriter.Write("(" + "\"" + varStringer x + "\"" + " " + string i + ") ")
                | BoolValue true -> strWriter.Write("\"" + varStringer x + "\"" + " ")
                | BoolValue false -> ()
            )

            strWriter.Write("}")

            strWriter.Write('\n')

            for x in sucs do
                strWriter.Write(string (x) + " ")

            strWriter.Write('\n')

        strWriter.Write("--END--\n")

        strWriter.ToString()


    let computeBisimulationQuotient (ts : TransitionSystem<'L>) =
        // Helper function to split a part of the partition
        let splitPartition (stateToPartitionId : Map<int, int>) partitionId =
            let statesInPartitionId =
                stateToPartitionId
                |> Map.toSeq
                |> Seq.filter (fun (_, x) -> x = partitionId)
                |> Seq.map fst

            if Seq.length statesInPartitionId <= 1 then
                // This partition contains only one state, cannot be split further
                None
            else

                let c =
                    statesInPartitionId
                    // Map all states to the successor partitions
                    |> Seq.map (fun s ->
                        let sucPartitions = ts.Edges.[s] |> Set.map (fun s' -> stateToPartitionId.[s'])
                        sucPartitions, s
                    )
                    |> Seq.groupBy fst
                    |> Seq.map (fun (k, el) -> k, Seq.map snd el |> set)
                    |> Map.ofSeq

                if Map.count c = 1 then
                    // All states point to the same set of partitions, no need to split
                    None
                else
                    Map.values c |> seq |> Some

        // We init the partition based only on the AP evaluation of each state
        let isAcceptingState s =
                match ts.AcceptingStates with
                | None -> true
                | Some accepts -> Set.contains s accepts
            
        let initStateToPartitionId =
            ts.States
            |> Seq.groupBy (fun s -> (ts.VariableEval.[s],isAcceptingState s))
            |> Seq.map snd
            |> Seq.mapi (fun i states -> states |> Seq.map (fun s -> s, i))
            |> Seq.concat
            |> Map.ofSeq

        let rec iterativeSplit (stateToPartitionId : Map<int, int>) : Map<int, int> =
            let partitionIDs = stateToPartitionId |> Map.toSeq |> Seq.map snd |> Seq.distinct

            let mutable freshId = Seq.max partitionIDs + 1

            // Use laziness here to not do all the work
            partitionIDs
            |> Seq.choose (fun id -> splitPartition stateToPartitionId id)
            |> Seq.tryHead
            |> function
                | None ->
                    // We are done, nothing left to split
                    stateToPartitionId
                | Some newPartitions ->

                    let newSplit =
                        (stateToPartitionId, newPartitions)
                        ||> Seq.fold (fun m states ->
                            let newId = freshId
                            freshId <- freshId + 1

                            (m, states)
                            ||> Set.fold (fun mm s ->
                                // Overwrite the partitionID for s
                                Map.add s newId mm
                            )
                        )

                    iterativeSplit newSplit


        let finalStateToPartitionId = iterativeSplit initStateToPartitionId

        let states = Map.values finalStateToPartitionId |> set

        let partitionIdToStates =
            finalStateToPartitionId
            |> Map.toSeq
            |> Seq.groupBy snd
            |> Seq.map (fun (k, v) -> k, Seq.map fst v |> set)
            |> Map.ofSeq

        let newTs =
            {
                TransitionSystem.InitialStates = ts.InitialStates |> Set.map (fun x -> finalStateToPartitionId.[x])
                TransitionSystem.AcceptingStates = Option.map (fun xs -> xs |> Set.map (fun x -> finalStateToPartitionId.[x])) ts.AcceptingStates
                States = states
                VariableType = ts.VariableType
                Edges =
                    states
                    |> Seq.map (fun id ->
                        let sucPartitions =
                            partitionIdToStates.[id]
                            |> Seq.map (fun s -> ts.Edges.[s])
                            |> Seq.concat
                            |> Seq.map (fun s -> finalStateToPartitionId.[s])
                            |> set

                        id, sucPartitions
                    )
                    |> Map.ofSeq

                VariableEval =
                    states
                    |> Seq.map (fun id ->
                        let apEval =
                            finalStateToPartitionId
                            |> Map.toSeq
                            // Find some state in this partition
                            |> Seq.find (fun (_, idd) -> id = idd)
                            |> fun (s, _) -> ts.VariableEval.[s]

                        id, apEval
                    )
                    |> Map.ofSeq
            }

        newTs, finalStateToPartitionId


type TransitionSystemWithPrinter<'L when 'L : comparison> =
    {
        TransitionSystem : TransitionSystem<'L>
        Printer : Map<int, string>
    }


module Parser =
    open FParsec

    let ws = spaces


    let transitionSystemParser variableParser =

        let escapedVariableParser = between (skipChar '"') (skipChar '"') variableParser

        let variablesTypeParser =
            let variableTypeParser = stringReturn "Int" Int <|> stringReturn "Bool" Bool

            let variableTypePair =
                between
                    (skipChar '(' .>> ws)
                    (ws >>. skipChar ')')
                    (tuple2 escapedVariableParser (ws >>. variableTypeParser))

            many (variableTypePair .>> ws) |>> Map.ofList

        let variableEvalParser =
            let intEvalParser =
                between
                    (skipChar '(' .>> ws)
                    (ws >>. skipChar ')')
                    (tuple2 escapedVariableParser (ws >>. pint32 |>> IntValue))

            let boolEvalFullParser =
                let boolParser = stringReturn "true" true <|> stringReturn "false" false <|> stringReturn "t" true <|> stringReturn "f" false

                between
                    (skipChar '(' .>> ws)
                    (ws >>. skipChar ')')
                    (tuple2 escapedVariableParser (ws >>. boolParser |>> BoolValue))

            let boolEvalShortParser = escapedVariableParser |>> fun x -> (x, BoolValue true)

            let evalParser =
                choice [ (attempt intEvalParser); boolEvalFullParser; boolEvalShortParser ]

            between (skipChar '{' .>> ws) (skipChar '}') (many (evalParser .>> ws))
            |>> Map.ofList

        let stateParser =
            pstring "State:"
            >>. pipe3
                (ws >>. pint32)
                (ws >>. variableEvalParser)
                (ws >>. many (pint32 .>> ws))
                (fun id ap sucs -> (id, (sucs, ap)))

        let bodyParser = ws >>. many (stateParser .>> ws)

        pipe4
            (ws >>. skipString "Variables:" >>. ws >>. variablesTypeParser)
            (ws >>. skipString "Init:" >>. ws >>. many (pint32 .>> ws))
            (opt (ws >>. skipString "Accepting:" >>. ws >>. many (pint32 .>> ws)))
            (ws >>. skipString "--BODY--" >>. bodyParser .>> ws .>> skipString "--END--")
            (fun variableTypes init accept st ->
                {
                    TransitionSystem.States = st |> List.map fst |> set
                    InitialStates = set init
                    AcceptingStates = Option.map (fun x -> set x) accept
                    VariableType = variableTypes
                    Edges = st |> List.map (fun (k, (a, _)) -> k, set a) |> Map.ofList
                    VariableEval = st |> List.map (fun (k, (_, b)) -> k, b) |> Map.ofList
                }
            )

    let variableParser = many1Chars (letter <|> digit <|> pchar '#' <|> pchar '_' <|> pchar '-' <|> pchar '[' <|> pchar ']')

    let parseTransitionSystem (s : string) =
        let full = transitionSystemParser variableParser .>> spaces .>> eof
        let res = run full s

        match res with
        | Success(res, _, _) -> Result.Ok res
        | Failure(err, _, _) -> Result.Error err
