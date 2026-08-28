import Huarongdao.CorridorExport

open Huarongdao

def stateJson (key : State → String) (id : Nat) (state : State)
    (distance : Nat) : String :=
  let positions := String.intercalate "," <| Piece.all.map fun p =>
    let pos := state.pos p
    "[" ++ toString pos.x ++ "," ++ toString pos.y ++ "]"
  "{\"id\":" ++ toString id ++ ",\"key\":\"" ++ key state ++
    "\",\"positions\":[" ++ positions ++ "],\"distance\":" ++ toString distance ++
    ",\"goal\":" ++ toString (goal state) ++ "}"

def edgeJson (edge : Edge) : String :=
  "{\"source\":" ++ toString edge.source ++ ",\"target\":" ++ toString edge.target ++
  ",\"piece\":" ++ toString edge.piece.index ++ ",\"direction\":\"" ++
  edge.direction.label ++ "\"}"

def corridorStateJson (id mirrorId : Nat) (state : State)
    (primitiveDistance operationDistance : Nat) : String :=
  let positions := String.intercalate "," <| Piece.all.map fun p =>
    let pos := state.pos p
    "[" ++ toString pos.x ++ "," ++ toString pos.y ++ "]"
  "{\"id\":" ++ toString id ++ ",\"key\":\"" ++ State.key state ++
    "\",\"positions\":[" ++ positions ++ "],\"distance\":" ++
    toString primitiveDistance ++ ",\"goal\":" ++ toString (goal state) ++
    ",\"mirrorId\":" ++ toString mirrorId ++
    ",\"primitiveDistance\":" ++ toString primitiveDistance ++
    ",\"operationDistance\":" ++ toString operationDistance ++ "}"

def corridorEdgeJson (edge : CorridorExportEdge) : String :=
  let first := edge.steps.getD 0 ⟨0, 0, .caoCao, .up⟩
  let path := String.intercalate "," <| edge.path.toList.map toString
  let steps := String.intercalate "," <| edge.steps.toList.map edgeJson
  "{\"source\":" ++ toString edge.source ++ ",\"target\":" ++
    toString edge.target ++ ",\"piece\":" ++ toString first.piece.index ++
    ",\"direction\":\"" ++ first.direction.label ++ "\",\"weight\":" ++
    toString edge.steps.size ++ ",\"path\":[" ++ path ++
    "],\"steps\":[" ++ steps ++ "]}"

def minDistance (distances : Array Nat) (indices : Array Nat) : Nat :=
  indices.toList.foldl (fun current index =>
    min current (distances.getD index 0)) 1000000000

def corridorGoalIndices (graph : Graph) (corridor : CorridorExport) :
    Array Nat := Id.run do
  let mut goals : Array Nat := #[]
  for id in List.range corridor.anchors.size do
    let mirrorId := corridor.anchors.getD id 0
    if goal (graph.states.getD mirrorId classic) then
      goals := goals.push id
  return goals

def corridorGraphJson (graph : Graph) (corridor : CorridorExport) : String :=
  let operationDistances := corridorOperationDistances corridor
  let goalIndices := corridorGoalIndices graph corridor
  let goalMirrorIndices := goalIndices.map
    (fun id => corridor.anchors.getD id 0)
  let states := String.intercalate "," <|
    corridor.anchors.toList.mapIdx fun id mirrorId =>
      corridorStateJson id mirrorId
        (graph.states.getD mirrorId classic)
        (graph.distance.getD mirrorId 0)
        (operationDistances.getD id 0)
  let edges := String.intercalate "," <|
    corridor.edges.toList.map fun edge =>
      let source := (findIndex? corridor.anchors edge.source).getD 0
      let target := (findIndex? corridor.anchors edge.target).getD 0
      corridorEdgeJson
        { edge with source := source, target := target }
  let goals := corridor.anchors.toList.mapIdx (fun id mirrorId =>
      if goal (graph.states.getD mirrorId classic) then toString id else "")
    |>.filter (fun value => !value.isEmpty)
  let primitiveGoalDistance :=
    minDistance graph.distance goalMirrorIndices
  let operationGoalDistance :=
    minDistance operationDistances goalIndices
  "{\"meta\":{\"width\":4,\"height\":5,\"initial\":0,\"stateCount\":" ++
    toString corridor.anchors.size ++ ",\"edgeCount\":" ++
    toString corridor.edges.size ++ ",\"goals\":[" ++
    String.intercalate "," goals ++
    "],\"stateSpace\":\"forced_corridor\",\"parent\":\"graph.mirror.json\"" ++
    ",\"parentStateCount\":" ++ toString graph.states.size ++
    ",\"parentEdgeCount\":" ++ toString graph.edges.size ++
    ",\"suppressedStateCount\":" ++
    toString (graph.states.size - corridor.anchors.size) ++
    ",\"primitiveShortestGoalDistance\":" ++
    toString primitiveGoalDistance ++
    ",\"operationShortestGoalDistance\":" ++
    toString operationGoalDistance ++
    ",\"parentDirectedAdjacencyCount\":" ++
    toString (directedAdjacencyCount graph) ++
    ",\"parentParallelEdgeCount\":" ++
    toString (graph.edges.size - directedAdjacencyCount graph) ++
    ",\"parentAdjacencyIntegrity\":\"sound_and_complete\"" ++
    ",\"parentEdgeLabelPolicy\":\"one_representative_per_directed_adjacency\"" ++
    ",\"verified\":true,\"generator\":\"Lean buildCorridorExport\"" ++
    "},\"states\":[" ++ states ++ "],\"edges\":[" ++ edges ++ "]}"

def graphJson (key : State → String) (quotient : String) (graph : Graph) : String :=
  let states := String.intercalate "," <| graph.states.toList.mapIdx fun id state =>
    stateJson key id state (graph.distance.getD id 0)
  let edges := String.intercalate "," <| graph.edges.toList.map edgeJson
  let goals := graph.states.toList.mapIdx (fun id s => (id, s))
    |>.filter (fun pair => goal pair.2)
    |>.map (fun pair => toString pair.1)
  "{\"meta\":{\"width\":4,\"height\":5,\"initial\":0,\"stateCount\":" ++
    toString graph.states.size ++ ",\"edgeCount\":" ++ toString graph.edges.size ++
    ",\"goals\":[" ++ String.intercalate "," goals ++ "]" ++ quotient ++
    "},\"states\":[" ++ states ++
    "],\"edges\":[" ++ edges ++ "]}"

def main (args : List String) : IO UInt32 := do
  let output := args.head?.getD "frontend/graph.json"
  let mode := args.drop 1 |>.head?.getD "shape"
  if mode == "corridor" then
    IO.println "Building and checking the corridor graph in Lean..."
    let graph := enumerateMirror
    if !checkMirrorEdgesComplete graph then
      IO.eprintln "Mirror edge completeness certificate failed."
      return 1
    let corridor := buildCorridorExport graph
    if !checkCorridorExport graph corridor then
      IO.eprintln "Corridor segmentation certificate failed."
      let neighbours := graph.neighbourTable
      IO.eprintln s!"parent endpoints: {graphEdgeEndpointsValid graph}"
      IO.eprintln s!"parent edges complete: {checkMirrorEdgesComplete graph}"
      IO.eprintln s!"parent reversible: {checkMirrorReversible graph}"
      IO.eprintln s!"anchors valid: {checkCorridorAnchors graph neighbours corridor.anchors}"
      IO.eprintln s!"trace complete: {corridor.complete}"
      IO.eprintln s!"paths valid: {corridor.edges.all (checkCorridorPath graph neighbours corridor.anchors)}"
      IO.eprintln s!"paths partition: {checkCorridorAdjacencyPartition graph corridor}"
      return 1
    IO.FS.writeFile output (corridorGraphJson graph corridor)
    IO.println s!"Wrote {corridor.anchors.size} anchors and {corridor.edges.size} macro moves to {output}"
    return 0
  let isMirror := mode == "mirror"
  IO.println s!"Enumerating the {mode} state graph in Lean..."
  let graph := if isMirror then enumerateMirror else enumerate classic
  if isMirror && !checkMirrorEdgesComplete graph then
    IO.eprintln "Mirror edge integrity certificate failed; refusing to export."
    return 1
  let key := if isMirror then mirrorKey else State.key
  let quotient :=
    if isMirror then
      let parent := enumerate classic
      ",\"quotient\":{\"symmetry\":\"horizontal_mirror\",\"parent\":\"graph.json\"" ++
        ",\"originalStateCount\":" ++ toString parent.states.size ++
        ",\"originalEdgeCount\":" ++ toString parent.edges.size ++
        "},\"verified\":true,\"edgeIntegrity\":\"sound_and_complete\""
    else
      ""
  IO.FS.writeFile output (graphJson key quotient graph)
  IO.println s!"Wrote {graph.states.size} states and {graph.edges.size} directed moves to {output}"
  return 0
