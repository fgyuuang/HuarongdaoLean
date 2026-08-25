import Huarongdao.Generic

open SlidingPuzzle Huarongdao

private def natAt (args : Array String) (index : Nat) : Option Nat :=
  (args[index]?).bind String.toNat?

private def parseRequest (tokens : Array String) : Option (PuzzleSpec × SearchConfig) := do
  let width ← natAt tokens 0
  let height ← natAt tokens 1
  let maxStates ← natAt tokens 2
  let maxDepth ← natAt tokens 3
  let count ← natAt tokens 4
  let expected := 5 + count * 6
  if tokens.size != expected && tokens.size != expected + 1 then none else
    let mut shapes : Array Shape := #[]
    let mut positions : Array Pos := #[]
    let mut goals : Array (Option Pos) := #[]
    for block in List.range count do
      let base := 5 + block * 6
      let shapeWidth ← natAt tokens base
      let shapeHeight ← natAt tokens (base + 1)
      let x ← natAt tokens (base + 2)
      let y ← natAt tokens (base + 3)
      let goalX := tokens[base + 4]!
      let goalY := tokens[base + 5]!
      let goal ← if goalX == "*" && goalY == "*" then
        some none
      else do
        let gx ← goalX.toNat?
        let gy ← goalY.toNat?
        some (some ⟨gx, gy⟩)
      shapes := shapes.push ⟨shapeWidth, shapeHeight⟩
      positions := positions.push ⟨x, y⟩
      goals := goals.push goal
    let strategy ← if tokens.size == expected then some SearchStrategy.bfs else
      match tokens[expected]? with
      | some "astar" => some SearchStrategy.astar
      | some "bfs" => some SearchStrategy.bfs
      | _ => none
    some (⟨width, height, shapes, ⟨positions⟩, ⟨goals⟩⟩, ⟨maxStates, maxDepth, strategy⟩)

private def statusName : SearchStatus → String
  | .invalid => "invalid"
  | .solved => "solved"
  | .unreachable => "unreachable"
  | .limit => "limit"

private def strategyName : SearchStrategy → String
  | .bfs => "bfs"
  | .astar => "astar"

private def directionName : Direction → String
  | .up => "up" | .down => "down" | .left => "left" | .right => "right"

private def quote (value : String) : String :=
  String.ofList ['"'] ++ value ++ String.ofList ['"']

private def field (name value : String) : String := quote name ++ ":" ++ value

private def positionJson (position : Pos) : String :=
  "{" ++ field "x" (toString position.x) ++ "," ++ field "y" (toString position.y) ++ "}"

private def stateJson (state : SlidingPuzzle.State) : String :=
  "{" ++ field "positions" ("[" ++ String.intercalate "," (state.positions.toList.map positionJson) ++ "]") ++ "}"

private def actionJson (step : Nat) (action : SlidingPuzzle.Action) : String :=
  "{" ++ field "step" (toString step) ++ "," ++
    field "block" (toString (action.block + 1)) ++ "," ++
    field "direction" (quote (directionName action.direction)) ++ "}"

private def trace (spec : PuzzleSpec) : SlidingPuzzle.State → List SlidingPuzzle.Action → Option (List SlidingPuzzle.State)
  | state, [] => some [state]
  | state, action :: rest => do
      let next ← tryMove spec state action.block action.direction
      let tail ← trace spec next rest
      some (state :: tail)

private def graphNodeJson (spec : PuzzleSpec) (graph : StateGraph)
    (index : Nat) (state : SlidingPuzzle.State) : String :=
  "{" ++ field "id" (toString index) ++ "," ++
    field "distance" (toString (graph.distance.getD index 0)) ++ "," ++
    field "goal" (toString (goalMatches spec state)) ++ "," ++
    field "positions" ("[" ++ String.intercalate "," (state.positions.toList.map positionJson) ++ "]") ++ "}"

private def graphEdgeJson (edge : GraphEdge) : String :=
  "{" ++ field "source" (toString edge.source) ++ "," ++
    field "target" (toString edge.target) ++ "," ++
    field "block" (toString (edge.action.block + 1)) ++ "," ++
    field "direction" (quote (directionName edge.action.direction)) ++ "}"

private def resultJson (spec : PuzzleSpec) (result : SearchResult) : String :=
  let graph := result.graph
  let verified := result.verified spec
  let actionData := result.actions.mapIdx fun index action => actionJson (index + 1) action
  let stateData := (trace spec spec.initial result.actions).getD [] |>.map stateJson
  let nodeData := graph.states.toList.mapIdx fun index state => graphNodeJson spec graph index state
  let edgeData := graph.edges.toList.map graphEdgeJson
  let edgeVerified := graph.checkEdges spec
  let validation := "{" ++ field "wellFormed" (toString (wellFormed spec)) ++ "," ++
    field "validInitial" (toString (valid spec spec.initial)) ++ "," ++
    field "goalDefined" (toString (goalDefined spec)) ++ "," ++
    field "goalWellFormed" (toString (goalWellFormed spec)) ++ "}"
  let stats := "{" ++ field "visitedStates" (toString graph.states.size) ++ "," ++
    field "expandedStates" (toString graph.expanded) ++ "," ++
    field "generatedTransitions" (toString graph.generated) ++ "," ++
    field "shortestLength" (if result.status == .solved then toString result.actions.length else "null") ++ "," ++
    field "truncated" (toString graph.truncated) ++ "," ++
    field "algorithm" (quote (strategyName result.strategy)) ++ "," ++
    field "heuristic" (if result.strategy == .astar then quote "weighted-manhattan+shape-goal-symmetry" else "null") ++ "}"
  let graphJson := "{" ++ field "complete" (toString graph.complete) ++ "," ++
    field "truncated" (toString graph.truncated) ++ "," ++
    field "kind" (quote (if graph.complete then "reachable-graph" else if graph.truncated then "truncated-subgraph" else "solution-subgraph")) ++ "," ++
    field "edgesVerified" (toString edgeVerified) ++ "," ++
    field "nodes" ("[" ++ String.intercalate "," nodeData ++ "]") ++ "," ++
    field "edges" ("[" ++ String.intercalate "," edgeData ++ "]") ++ "}"
  let solution := if result.status == .solved then
    "{" ++ field "actions" ("[" ++ String.intercalate "," actionData ++ "]") ++ "," ++
      field "states" ("[" ++ String.intercalate "," stateData ++ "]") ++ "}"
    else "null"
  let proof := if result.status == .solved then
    "{" ++ field "kind" (quote "path-certificate") ++ "," ++
      field "verified" (toString verified) ++ "," ++
      field "verifier" (quote "Lean checkSolution") ++ "," ++
      field "claim" (quote "Nonempty (Solution spec)") ++ "," ++
      field "shortest" ("{" ++ field "computedBySearch" "true" ++ "," ++
        field "algorithm" (quote (strategyName result.strategy)) ++ "," ++ field "kernelProved" "false" ++ "}") ++ "}"
    else "null"
  "{" ++ field "schemaVersion" (quote "2") ++ "," ++
    field "status" (quote (statusName result.status)) ++ "," ++
    field "validation" validation ++ "," ++ field "stats" stats ++ "," ++
    field "graph" graphJson ++ "," ++ field "solution" solution ++ "," ++ field "proof" proof ++ "}"

private def errorJson (message : String) : String :=
  "{" ++ field "schemaVersion" (quote "1") ++ "," ++ field "status" (quote "invalid") ++ "," ++
    field "error" ("{" ++ field "code" (quote "INVALID_REQUEST") ++ "," ++
      field "message" (quote message) ++ "}") ++ "}"

def main (args : List String) : IO UInt32 := do
  match parseRequest args.toArray with
  | none =>
      IO.println (errorJson "Expected width height maxStates maxDepth count, six fields per block, optional bfs|astar")
      return 2
  | some (spec, config) =>
      let result := search spec config
      IO.println (resultJson spec result)
      return 0
