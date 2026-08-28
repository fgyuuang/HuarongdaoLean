import Huarongdao

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
  let isMirror := mode == "mirror"
  IO.println s!"Enumerating the {mode} state graph in Lean..."
  let graph := if isMirror then enumerateMirror else enumerate classic
  let key := if isMirror then mirrorKey else State.key
  let quotient :=
    if isMirror then
      ",\"quotient\":{\"symmetry\":\"horizontal_mirror\",\"parent\":\"graph.json\"}"
    else
      ""
  IO.FS.writeFile output (graphJson key quotient graph)
  IO.println s!"Wrote {graph.states.size} states and {graph.edges.size} directed moves to {output}"
  return 0
