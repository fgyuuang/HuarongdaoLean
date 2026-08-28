import Huarongdao.CorridorCompression
import Huarongdao.MirrorSearch
import Std.Data.HashSet

namespace Huarongdao

/-
The rendered corridor graph is a finite presentation of the verified mirror
graph.  This module owns both the deterministic segmentation algorithm and the
checks that make the presentation safe to export.  The dependent
`CorridorMacroStep` definitions in `CorridorCompression.lean` remain the
semantic interface; this file is the executable finite witness used by the
visualizer.
-/

structure CorridorExportEdge where
  source : Nat
  target : Nat
  path : Array Nat
  steps : Array Edge
  deriving Repr, DecidableEq

structure CorridorExport where
  anchors : Array Nat
  edges : Array CorridorExportEdge
  complete : Bool
  deriving Repr

structure CorridorPathTrace where
  paths : Array (Array Nat)
  complete : Bool
  deriving Repr

def arrayContainsNat (values : Array Nat) (value : Nat) : Bool :=
  values.any (fun candidate => candidate == value)

def addUniqueNat (values : Array Nat) (value : Nat) : Array Nat :=
  if arrayContainsNat values value then values else values.push value

def Graph.neighbourTable (graph : Graph) : Array (Array Nat) := Id.run do
  let mut table : Array (Array Nat) :=
    Array.replicate graph.states.size #[]
  for edge in graph.edges do
    if edge.source < graph.states.size &&
        edge.target < graph.states.size &&
        edge.source != edge.target then
      let sourceNeighbours := table.getD edge.source #[]
      table := table.set! edge.source
        (addUniqueNat sourceNeighbours edge.target)
      let targetNeighbours := table.getD edge.target #[]
      table := table.set! edge.target
        (addUniqueNat targetNeighbours edge.source)
  return table

def undirectedKey (nodeCount left right : Nat) : Nat :=
  let low := min left right
  let high := max left right
  low * nodeCount + high

def directedKey (nodeCount source target : Nat) : Nat :=
  source * nodeCount + target

/-!
The corridor layer forgets action labels and keeps one representative for each
directed endpoint adjacency.  The mirror layer separately certifies every
stored action edge, including parallel edges with the same endpoints.
-/
def directedAdjacencyCount (graph : Graph) : Nat :=
  graph.neighbourTable.toList.foldl
    (fun count neighbours => count + neighbours.size) 0

def graphEdgeEndpointsValid (graph : Graph) : Bool :=
  graph.edges.all fun edge =>
    edge.source < graph.states.size &&
      edge.target < graph.states.size

def Graph.firstEdge? (graph : Graph) (source target : Nat) :
    Option Edge := Id.run do
  for edge in graph.edges do
    if edge.source == source && edge.target == target then
      return some edge
  return none

def findIndex? (values : Array Nat) (value : Nat) : Option Nat := Id.run do
  let mut index := 0
  for candidate in values do
    if candidate == value then
      return some index
    index := index + 1
  return none

def corridorAnchors
    (graph : Graph) (neighbours : Array (Array Nat)) : Array Nat := Id.run do
  let mut anchors : Array Nat := #[]
  for index in List.range graph.states.size do
    let state := graph.states.getD index classic
    let degree := (neighbours.getD index #[]).size
    if index == 0 || goal state || degree != 2 then
      anchors := anchors.push index
  return anchors

def allUndirectedEdgesVisited
    (graph : Graph) (visited : Std.HashSet Nat) : Bool :=
  graph.edges.all fun edge =>
    edge.source == edge.target ||
      visited.contains (undirectedKey graph.states.size edge.source edge.target)

def traceCorridors
    (graph : Graph) (neighbours : Array (Array Nat))
    (anchors : Array Nat) : CorridorPathTrace := Id.run do
  let mut visited : Std.HashSet Nat := {}
  let mut paths : Array (Array Nat) := #[]
  let mut complete := true
  for source in anchors do
    for first in neighbours.getD source #[] do
      let key := undirectedKey graph.states.size source first
      if complete && !visited.contains key then
        visited := visited.insert key
        let mut path : Array Nat := #[source, first]
        let mut previous := source
        let mut current := first
        let mut segmentOk := true
        while segmentOk &&
            !arrayContainsNat anchors current do
          let mut choices : Array Nat := #[]
          for candidate in neighbours.getD current #[] do
            if candidate != previous then
              choices := choices.push candidate
          if choices.size != 1 then
            segmentOk := false
          else
            let next := choices.getD 0 current
            let nextKey :=
              undirectedKey graph.states.size current next
            if visited.contains nextKey then
              segmentOk := false
            else
              visited := visited.insert nextKey
              path := path.push next
              previous := current
              current := next
        if segmentOk && arrayContainsNat anchors current then
          paths := paths.push path
        else
          complete := false
  complete := complete && allUndirectedEdgesVisited graph visited
  return ⟨paths, complete⟩

def corridorPathSteps
    (graph : Graph) (path : Array Nat) : Option (Array Edge) := Id.run do
  if path.size < 2 then
    return none
  let mut steps : Array Edge := #[]
  let mut valid := true
  for index in List.range (path.size - 1) do
    let source := path.getD index 0
    let target := path.getD (index + 1) 0
    match graph.firstEdge? source target with
    | none => valid := false
    | some edge => steps := steps.push edge
  if valid then some steps else none

def makeCorridorExportEdge
    (graph : Graph) (path : Array Nat) :
    Option CorridorExportEdge := do
  let steps ← corridorPathSteps graph path
  return {
    source := path.getD 0 0
    target := path.getD (path.size - 1) 0
    path := path
    steps := steps
  }

def buildCorridorExport (graph : Graph) : CorridorExport := Id.run do
  let neighbours := graph.neighbourTable
  let anchors := corridorAnchors graph neighbours
  let trace := traceCorridors graph neighbours anchors
  let mut edges : Array CorridorExportEdge := #[]
  let mut complete := trace.complete
  for path in trace.paths do
    match makeCorridorExportEdge graph path with
    | none => complete := false
    | some edge => edges := edges.push edge
    let reversed := path.toList.reverse.toArray
    match makeCorridorExportEdge graph reversed with
    | none => complete := false
    | some edge => edges := edges.push edge
  return ⟨anchors, edges, complete⟩

def checkCorridorAnchor
    (graph : Graph) (neighbours : Array (Array Nat))
    (anchors : Array Nat) (index : Nat) : Bool :=
  index < graph.states.size &&
    (index == 0 ||
      goal (graph.states.getD index classic) ||
      (neighbours.getD index #[]).size != 2) &&
    arrayContainsNat anchors index

def checkUniqueNatArray (values : Array Nat) : Bool := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut unique := true
  for value in values do
    if seen.contains value then
      unique := false
    else
      seen := seen.insert value
  return unique

def checkCorridorAnchors
    (graph : Graph) (neighbours : Array (Array Nat))
    (anchors : Array Nat) : Bool :=
  anchors.size > 0 &&
    anchors.getD 0 1 == 0 &&
    checkUniqueNatArray anchors &&
    anchors.all (checkCorridorAnchor graph neighbours anchors)

def checkCorridorPath
    (graph : Graph) (neighbours : Array (Array Nat))
    (anchors : Array Nat) (edge : CorridorExportEdge) : Bool := Id.run do
  let path := edge.path
  if path.size < 2 then
    return false
  let source := path.getD 0 0
  let target := path.getD (path.size - 1) 0
  if edge.source != source || edge.target != target then
    return false
  if !arrayContainsNat anchors source ||
      !arrayContainsNat anchors target then
    return false
  if edge.steps.size != path.size - 1 then
    return false
  for index in List.range path.size do
    let node := path.getD index 0
    if node >= graph.states.size then
      return false
    if index > 0 && index + 1 < path.size &&
        arrayContainsNat anchors node then
      return false
  for index in List.range (path.size - 1) do
    let source := path.getD index 0
    let target := path.getD (index + 1) 0
    let neighbour := (neighbours.getD source #[]).any (fun node =>
      node == target)
    if !neighbour then
      return false
    let step := edge.steps.getD index
      ⟨0, 0, .caoCao, .up⟩
    if step.source != source || step.target != target ||
        !graphEdgeEndpointsValid graph ||
        !graph.edges.toList.contains step ||
        !checkMirrorEdge graph step then
      return false
  return true

/-!
The exported paths must form an exact directed adjacency partition of the
parent graph. Checking both directions explicitly prevents a one-way macro
export from passing merely because its underlying undirected edge is present.
-/
def checkCorridorAdjacencyPartition
    (graph : Graph) (corridor : CorridorExport) : Bool := Id.run do
  let neighbours := graph.neighbourTable
  let mut assigned : Std.HashSet Nat := {}
  let mut unique := true
  for corridorEdge in corridor.edges do
    if corridorEdge.path.size < 2 then
      unique := false
    else
      for index in List.range (corridorEdge.path.size - 1) do
        let source := corridorEdge.path.getD index 0
        let target := corridorEdge.path.getD (index + 1) 0
        let key := directedKey graph.states.size source target
        if assigned.contains key then
          unique := false
        else
          assigned := assigned.insert key
  let mut covered := true
  for source in List.range graph.states.size do
    for target in neighbours.getD source #[] do
      if !assigned.contains
          (directedKey graph.states.size source target) then
        covered := false
  return unique && covered

def checkMirrorReversible (graph : Graph) : Bool :=
  graphEdgeEndpointsValid graph &&
    graph.edges.all fun edge =>
      edge.source == edge.target ||
        graph.edges.any (fun reverse =>
          reverse.source == edge.target &&
            reverse.target == edge.source)

def checkCorridorExport (graph : Graph) (corridor : CorridorExport) : Bool :=
  let neighbours := graph.neighbourTable
  graphEdgeEndpointsValid graph &&
    checkMirrorEdgesComplete graph &&
    checkMirrorReversible graph &&
    checkCorridorAnchors graph neighbours corridor.anchors &&
    corridor.complete &&
    corridor.edges.all (checkCorridorPath graph neighbours corridor.anchors) &&
    checkCorridorAdjacencyPartition graph corridor

def corridorOperationDistances
    (corridor : CorridorExport) : Array Nat := Id.run do
  let mut adjacency : Array (Array Nat) :=
    Array.replicate corridor.anchors.size #[]
  for edge in corridor.edges do
    match findIndex? corridor.anchors edge.source,
        findIndex? corridor.anchors edge.target with
    | some source, some target =>
        let neighbours := adjacency.getD source #[]
        if !arrayContainsNat neighbours target then
          adjacency := adjacency.set! source (neighbours.push target)
    | _, _ => pure ()
  let mut distances : Array (Option Nat) :=
    Array.replicate corridor.anchors.size none
  if corridor.anchors.size > 0 then
    distances := distances.set! 0 (some 0)
  let mut queue : Array Nat := #[]
  if corridor.anchors.size > 0 then
    queue := queue.push 0
  let mut cursor := 0
  while cursor < queue.size do
    let source := queue.getD cursor 0
    let sourceDistance := (distances.getD source none).getD 0
    for target in adjacency.getD source #[] do
      if (distances.getD target none).isNone then
        distances := distances.set! target (some (sourceDistance + 1))
        queue := queue.push target
    cursor := cursor + 1
  return distances.map (fun distance => distance.getD 0)

theorem checkCorridorExport_sound
    {graph : Graph} {corridor : CorridorExport}
    (checked : checkCorridorExport graph corridor = true) :
    graphEdgeEndpointsValid graph = true ∧
      checkMirrorEdgesComplete graph = true ∧
      checkMirrorReversible graph = true ∧
      checkCorridorAnchors graph graph.neighbourTable corridor.anchors = true ∧
      corridor.complete = true ∧
      corridor.edges.all
        (checkCorridorPath graph graph.neighbourTable corridor.anchors) = true ∧
      checkCorridorAdjacencyPartition graph corridor = true := by
  unfold checkCorridorExport at checked
  simp only [Bool.and_eq_true] at checked
  exact ⟨checked.1.1.1.1.1.1, checked.1.1.1.1.1.2,
    checked.1.1.1.1.2, checked.1.1.1.2, checked.1.1.2,
    checked.1.2, checked.2⟩

end Huarongdao
