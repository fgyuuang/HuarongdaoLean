import Huarongdao

open Huarongdao

def stateJson (id : Nat) (state : State) (distance : Nat) : String :=
  let positions := String.intercalate "," <| Piece.all.map fun p =>
    let pos := state.pos p
    "[" ++ toString pos.x ++ "," ++ toString pos.y ++ "]"
  "{\"id\":" ++ toString id ++ ",\"key\":\"" ++ state.key ++
    "\",\"positions\":[" ++ positions ++ "],\"distance\":" ++ toString distance ++
    ",\"goal\":" ++ toString (goal state) ++ "}"

def edgeJson (edge : Edge) : String :=
  "{\"source\":" ++ toString edge.source ++ ",\"target\":" ++ toString edge.target ++
    ",\"piece\":" ++ toString edge.piece.index ++ ",\"direction\":\"" ++
    edge.direction.label ++ "\"}"

def graphJson (graph : Graph) : String :=
  let states := String.intercalate "," <| graph.states.toList.mapIdx fun id state =>
    stateJson id state (graph.distance.getD id 0)
  let edges := String.intercalate "," <| graph.edges.toList.map edgeJson
  let goals := graph.states.toList.mapIdx (fun id s => (id, s))
    |>.filter (fun pair => goal pair.2)
    |>.map (fun pair => toString pair.1)
  "{\"meta\":{\"width\":4,\"height\":5,\"initial\":0,\"stateCount\":" ++
    toString graph.states.size ++ ",\"edgeCount\":" ++ toString graph.edges.size ++
    ",\"goals\":[" ++ String.intercalate "," goals ++ "]},\"states\":[" ++ states ++
    "],\"edges\":[" ++ edges ++ "]}"

def main (args : List String) : IO UInt32 := do
  let output := args.head?.getD "frontend/graph.json"
  IO.println "Enumerating the reachable state graph in Lean..."
  let graph := enumerate classic
  IO.FS.writeFile output (graphJson graph)
  IO.println s!"Wrote {graph.states.size} states and {graph.edges.size} directed moves to {output}"
  return 0
