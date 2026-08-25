import Huarongdao.Generic.Enumeration
import Huarongdao.Generic.Paths
import Std.Data.HashMap

namespace SlidingPuzzle

inductive SearchStrategy where
  | bfs | astar
  deriving Repr, DecidableEq, BEq

structure SearchConfig where
  maxStates : Nat := 100000
  maxDepth : Nat := 500
  strategy : SearchStrategy := .astar
  deriving Repr, DecidableEq

inductive SearchStatus where
  | invalid | solved | unreachable | limit
  deriving Repr, DecidableEq, BEq

structure GraphEdge where
  source : Nat
  target : Nat
  action : Action
  deriving Repr, DecidableEq, BEq

structure StateGraph where
  states : Array State
  distance : Array Nat
  edges : Array GraphEdge
  expanded : Nat
  generated : Nat
  complete : Bool
  truncated : Bool
  deriving Repr

structure SearchResult where
  status : SearchStatus
  strategy : SearchStrategy
  graph : StateGraph
  actions : List Action
  target : Option State
  deriving Repr

private def emptyGraph : StateGraph := ⟨#[], #[], #[], 0, 0, false, false⟩

def checkSolution (spec : PuzzleSpec) (actions : List Action) : Bool :=
  match runMoves spec spec.initial actions with
  | none => false
  | some target => goalMatches spec target

theorem checkSolution_sound {spec : PuzzleSpec} {actions : List Action}
    (checked : checkSolution spec actions = true) : Solves spec actions := by
  unfold checkSolution at checked
  cases executed : runMoves spec spec.initial actions with
  | none => simp [executed] at checked
  | some target =>
      simp [executed] at checked
      exact ⟨target, executed, checked⟩

theorem checkSolution_iff {spec : PuzzleSpec} {actions : List Action} :
    checkSolution spec actions = true ↔ Solves spec actions := by
  constructor
  · exact checkSolution_sound
  · rintro ⟨target, executed, solved⟩
    simp [checkSolution, executed, solved]

def StateGraph.sourceState (spec : PuzzleSpec) (graph : StateGraph) (edge : GraphEdge) : State :=
  graph.states.getD edge.source spec.initial

def StateGraph.targetState (spec : PuzzleSpec) (graph : StateGraph) (edge : GraphEdge) : State :=
  graph.states.getD edge.target spec.initial

def StateGraph.checkEdge (spec : PuzzleSpec) (graph : StateGraph) (edge : GraphEdge) : Bool :=
  edge.source < graph.states.size && edge.target < graph.states.size &&
  tryMove spec (graph.sourceState spec edge) edge.action.block edge.action.direction ==
    some (graph.targetState spec edge)

theorem StateGraph.checkEdge_sound {spec : PuzzleSpec} {graph : StateGraph} {edge : GraphEdge}
    (checked : graph.checkEdge spec edge = true) :
    tryMove spec (graph.sourceState spec edge) edge.action.block edge.action.direction =
      some (graph.targetState spec edge) := by
  unfold StateGraph.checkEdge at checked
  simp only [Bool.and_eq_true] at checked
  exact beq_iff_eq.mp checked.2

def StateGraph.checkEdges (spec : PuzzleSpec) (graph : StateGraph) : Bool :=
  graph.edges.all (graph.checkEdge spec)

theorem StateGraph.checkEdges_sound {spec : PuzzleSpec} {graph : StateGraph}
    (checked : graph.checkEdges spec = true) (index : Nat) (hi : index < graph.edges.size) :
    tryMove spec (graph.sourceState spec graph.edges[index]) graph.edges[index].action.block
      graph.edges[index].action.direction = some (graph.targetState spec graph.edges[index]) := by
  apply StateGraph.checkEdge_sound
  exact (Array.all_eq_true.mp checked) index hi

/-- A proof-carrying path through an exported exact state graph. -/
inductive GraphPath (spec : PuzzleSpec) (graph : StateGraph) : State → State → Type where
  | nil (state : State) : GraphPath spec graph state state
  | cons {source next target : State} (edge : GraphEdge)
      (source_eq : graph.sourceState spec edge = source)
      (target_eq : graph.targetState spec edge = next)
      (checked : graph.checkEdge spec edge = true)
      (tail : GraphPath spec graph next target) : GraphPath spec graph source target

namespace GraphPath

def length : GraphPath spec graph source target → Nat
  | .nil _ => 0
  | .cons _ _ _ _ tail => tail.length + 1

end GraphPath

def coordinateDistance (a b : Nat) : Nat :=
  if a < b then b - a else a - b

/-- A lower bound that ignores blocking pieces and board congestion. -/
def goalManhattan (spec : PuzzleSpec) (state : State) : Nat :=
  (blockIds spec).foldl (fun total block =>
    match spec.goal.positions[block]? with
    | some (some goal) =>
        let here := state.pos block
        total + coordinateDistance here.x goal.x + coordinateDistance here.y goal.y
    | _ => total) 0

private def goalClassKey (spec : PuzzleSpec) (block : Nat) : String :=
  match spec.goal.positions[block]? with
  | some (some goal) => toString goal.x ++ ":" ++ toString goal.y
  | _ => "*"

/-- Canonical search key modulo permutations of blocks that have both the same
    rectangle shape and the same goal constraint. -/
def State.symmetryKey (state : State) (spec : PuzzleSpec) : String :=
  let tokens := (blockIds spec).map fun block =>
    let shape := spec.shape block
    let pos := state.pos block
    toString shape.width ++ "x" ++ toString shape.height ++ "@" ++
      goalClassKey spec block ++ "=" ++ toString pos.x ++ ":" ++ toString pos.y
  String.intercalate ";" tokens.mergeSort

def inTargetCorridor (shape : Huarongdao.Shape) (here goal cell : Huarongdao.Pos) : Bool :=
  min here.x goal.x ≤ cell.x && cell.x < max here.x goal.x + shape.width &&
  min here.y goal.y ≤ cell.y && cell.y < max here.y goal.y + shape.height

/-- Count other pieces intersecting a constrained block's swept bounding box. -/
def goalCorridorBlockers (spec : PuzzleSpec) (state : State) : Nat :=
  (blockIds spec).foldl (fun total block =>
    match spec.goal.positions[block]? with
    | some (some goal) =>
        let here := state.pos block
        let shape := spec.shape block
        total + (blockIds spec).foldl (fun count other =>
          if other == block then count else
          let cells := occupiedCells spec state other
          if cells.any (inTargetCorridor shape here goal) then count + 1 else count) 0
    | _ => total) 0

/-- Weighted guidance for fast feasible-path search. It is intentionally not
    used as a kernel-level shortest-path claim. -/
def informedScore (spec : PuzzleSpec) (state : State) (cost : Nat) : Nat :=
  cost + goalManhattan spec state * 8

structure OpenNode where
  priority : Nat
  cost : Nat
  stateId : Nat
  deriving Repr

private def OpenNode.before (a b : OpenNode) : Bool :=
  a.priority < b.priority ||
    (a.priority == b.priority && (a.cost < b.cost ||
      (a.cost == b.cost && a.stateId < b.stateId)))

private def heapPush (heap : Array OpenNode) (item : OpenNode) : Array OpenNode := Id.run do
  let mut result := heap.push item
  let mut index := result.size - 1
  while index > 0 do
    let parent := (index - 1) / 2
    if (result.getD index item).before (result.getD parent item) then
      let childValue := result.getD index item
      let parentValue := result.getD parent item
      result := result.set! index parentValue
      result := result.set! parent childValue
      index := parent
    else break
  return result

private def heapPop? (heap : Array OpenNode) : Option (OpenNode × Array OpenNode) := Id.run do
  if heap.isEmpty then return none
  let fallback := heap.getD 0 ⟨0, 0, 0⟩
  let root := fallback
  let last := heap.getD (heap.size - 1) fallback
  let mut result := heap.pop
  if !result.isEmpty then
    result := result.set! 0 last
    let mut index := 0
    let mut running := true
    while running do
      let left := index * 2 + 1
      if left >= result.size then break
      let right := left + 1
      let child := if right < result.size &&
          (result.getD right fallback).before (result.getD left fallback) then right else left
      if (result.getD child fallback).before (result.getD index fallback) then
        let childValue := result.getD child fallback
        let parentValue := result.getD index fallback
        result := result.set! child parentValue
        result := result.set! index childValue
        index := child
      else running := false
  return some (root, result)

private def reconstructActions (parents : Array (Option (Nat × Action))) (target : Nat) : List Action := Id.run do
  let mut result : List Action := []
  let mut current := target
  let mut running := true
  while running do
    match parents.getD current none with
    | none => running := false
    | some (parent, action) =>
        result := action :: result
        current := parent
  return result

/-- A* with a binary min-heap and lazy duplicate entries. The candidate path is
    still independently replayed by checkSolution before it becomes a proof. -/
def searchAStar (spec : PuzzleSpec) (config : SearchConfig := {}) : SearchResult := Id.run do
  if wellFormed spec != true then return ⟨.invalid, .astar, emptyGraph, [], none⟩
  let mut states := #[spec.initial]
  let mut costs := #[0]
  let mut parents : Array (Option (Nat × Action)) := #[none]
  let mut closed := #[false]
  let mut edges : Array GraphEdge := #[]
  let mut known : Std.HashMap String Nat := {}
  known := known.insert (spec.initial.symmetryKey spec) 0
  let mut frontier := heapPush #[] ⟨informedScore spec spec.initial 0, 0, 0⟩
  let mut expanded := 0
  let mut generated := 0
  let mut truncated := false
  let mut answer : Option Nat := none
  while !frontier.isEmpty && answer.isNone do
    let some (item, remaining) := heapPop? frontier | break
    frontier := remaining
    if item.cost != costs.getD item.stateId (item.cost + 1) || closed.getD item.stateId true then
      continue
    let state := states.getD item.stateId spec.initial
    if goalMatches spec state then
      answer := some item.stateId
      break
    if item.cost >= config.maxDepth then
      if !(legalMoves spec state).isEmpty then truncated := true
      closed := closed.set! item.stateId true
      continue
    closed := closed.set! item.stateId true
    expanded := expanded + 1
    for (action, next) in legalMoves spec state do
      generated := generated + 1
      let tentative := item.cost + 1
      let key := next.symmetryKey spec
      match known.get? key with
      | some target =>
          let exactTarget := states.getD target spec.initial == next
          if exactTarget then edges := edges.push ⟨item.stateId, target, action⟩
          if exactTarget && tentative < costs.getD target tentative then
            costs := costs.set! target tentative
            parents := parents.set! target (some (item.stateId, action))
            closed := closed.set! target false
            frontier := heapPush frontier ⟨informedScore spec next tentative, tentative, target⟩
      | none =>
          if states.size >= config.maxStates then
            truncated := true
          else
            let target := states.size
            known := known.insert key target
            states := states.push next
            costs := costs.push tentative
            parents := parents.push (some (item.stateId, action))
            closed := closed.push false
            edges := edges.push ⟨item.stateId, target, action⟩
            frontier := heapPush frontier ⟨informedScore spec next tentative, tentative, target⟩
  match answer with
  | some targetId =>
      let target := states.getD targetId spec.initial
      let actions := reconstructActions parents targetId
      let graph : StateGraph := ⟨states, costs, edges, expanded, generated, false, truncated⟩
      return ⟨.solved, .astar, graph, actions, some target⟩
  | none =>
      let complete := !truncated && frontier.isEmpty
      let graph : StateGraph := ⟨states, costs, edges, expanded, generated, complete, truncated⟩
      return ⟨if complete then .unreachable else .limit, .astar, graph, [], none⟩

def searchBfs (spec : PuzzleSpec) (config : SearchConfig := {}) : SearchResult := Id.run do
  if wellFormed spec != true then return ⟨.invalid, .bfs, emptyGraph, [], none⟩
  let mut states := #[spec.initial]
  let mut reversePaths : Array (List Action) := #[[]]
  let mut distances := #[0]
  let mut edges : Array GraphEdge := #[]
  let mut known : Std.HashMap String Nat := {}
  known := known.insert (spec.initial.key spec) 0
  let mut cursor := 0
  let mut expanded := 0
  let mut generated := 0
  let mut truncated := false
  let mut answer : Option (State × List Action) :=
    if goalMatches spec spec.initial then some (spec.initial, []) else none
  while cursor < states.size do
    if states.size ≥ config.maxStates then truncated := true; break
    let state := states.getD cursor spec.initial
    let reversePath := reversePaths.getD cursor []
    let depth := distances.getD cursor 0
    if depth < config.maxDepth then
      expanded := expanded + 1
      for (action, next) in legalMoves spec state do
        generated := generated + 1
        let key := next.key spec
        let target ← match known.get? key with
          | some id => pure id
          | none =>
              if states.size ≥ config.maxStates then
                truncated := true
                pure states.size
              else
                let id := states.size
                known := known.insert key id
                states := states.push next
                reversePaths := reversePaths.push (action :: reversePath)
                distances := distances.push (depth + 1)
                if answer.isNone && goalMatches spec next then
                  answer := some (next, (action :: reversePath).reverse)
                pure id
        if target < states.size then edges := edges.push ⟨cursor, target, action⟩
    else if !(legalMoves spec state).isEmpty then truncated := true
    cursor := cursor + 1
  let complete := !truncated && cursor ≥ states.size
  let graph : StateGraph := ⟨states, distances, edges, expanded, generated, complete, truncated⟩
  match answer with
  | some (target, actions) => return ⟨.solved, .bfs, graph, actions, some target⟩
  | none => return ⟨if complete then .unreachable else .limit, .bfs, graph, [], none⟩


def search (spec : PuzzleSpec) (config : SearchConfig := {}) : SearchResult :=
  match config.strategy with
  | .bfs => searchBfs spec config
  | .astar => searchAStar spec config

def SearchResult.verified (spec : PuzzleSpec) (result : SearchResult) : Bool :=
  result.status == .solved && checkSolution spec result.actions

theorem SearchResult.verified_solution {spec : PuzzleSpec} {result : SearchResult}
    (verified : result.verified spec = true) : Solves spec result.actions := by
  unfold SearchResult.verified at verified
  rw [Bool.and_eq_true] at verified
  exact checkSolution_sound verified.2

theorem verified_search_implies_exists {spec : PuzzleSpec} {result : SearchResult}
    (verified : result.verified spec = true) : Nonempty (Solution spec) := by
  have solves := result.verified_solution verified
  rw [solves_iff_nonempty_certified] at solves
  rcases solves with ⟨play, _⟩
  exact ⟨play.toSolution⟩

end SlidingPuzzle
