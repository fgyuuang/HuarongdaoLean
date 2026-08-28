import Huarongdao.CaoGuanGeometry
import Huarongdao.ClassicFullSpace

open Huarongdao
open Huarongdao.CaoGuanGeometry
open Huarongdao.ClassicFullSpace

structure FixedFiberRun where
  position : CaoPosition
  stateCount : Nat
  componentSizes : Array Nat
  componentDiameters : Array Nat
  directedEdgeCount : Nat
  movablePieceCounts : Array Nat
  deriving Repr

def caoPositions : List CaoPosition :=
  (List.finRange 4).flatMap fun y =>
    (List.finRange 3).map fun x => (x, y)

def rawCaoAt (state : State) (position : CaoPosition) : Bool :=
  decide (state.pos .caoCao = position.toPos)

def stateIdsAtCao (states : Array State) (position : CaoPosition) : List Nat :=
  (List.range states.size).filter fun stateId =>
    rawCaoAt (states.getD stateId classic) position

def stateHasCaoAt (states : Array State) (stateId : Nat)
    (position : CaoPosition) : Bool :=
  rawCaoAt (states.getD stateId classic) position

def targetIndexWithinCao
    (states : Array State) (index : Std.HashMap Nat Nat)
    (position : CaoPosition) (stateId : Nat)
    (piece : Piece) (direction : Direction) : Option Nat :=
  let source := states.getD stateId classic
  let occupancy := occupancyTable source
  match locallyLegalMove source occupancy piece direction with
  | none => none
  | some target =>
      if target.pos .caoCao = position.toPos then
        index.get? (placementCode target)
      else
        none

structure FixedFiberAdjacency where
  adjacency : Array (Array Nat)
  directedEdgeCount : Nat
  movablePieceCounts : Array Nat

def fixedFiberAdjacency
    (states : Array State) (position : CaoPosition) : FixedFiberAdjacency := Id.run do
  let index := placementIndex states
  let candidates := stateIdsAtCao states position
  let mut adjacency := Array.replicate states.size #[]
  let mut directedEdgeCount := 0
  let mut movablePieceCounts := Array.replicate Piece.all.length 0
  for candidateId in candidates do
    let mut neighbors : Array Nat := #[]
    let mut movableHere := Array.replicate Piece.all.length false
    for piece in Piece.all do
      for direction in Direction.all do
        match targetIndexWithinCao
            states index position candidateId piece direction with
        | none => pure ()
        | some targetId =>
            directedEdgeCount := directedEdgeCount + 1
            movableHere := movableHere.set! piece.index true
            if !(neighbors.contains targetId) then
              neighbors := neighbors.push targetId
    adjacency := adjacency.set! candidateId neighbors
    for piece in Piece.all do
      if movableHere.getD piece.index false then
        let count := movablePieceCounts.getD piece.index 0
        movablePieceCounts :=
          movablePieceCounts.set! piece.index (count + 1)
  return {
    adjacency := adjacency
    directedEdgeCount := directedEdgeCount
    movablePieceCounts := movablePieceCounts
  }

def fixedFiberComponents
    (states : Array State) (position : CaoPosition)
    (adjacency : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let candidates := stateIdsAtCao states position
  let mut seen := Array.replicate states.size false
  let mut components : Array (Array Nat) := #[]
  for candidateId in candidates do
    if !(seen.getD candidateId false) then
      let mut stack : Array Nat := #[candidateId]
      let mut members : Array Nat := #[]
      seen := seen.set! candidateId true
      while 0 < stack.size do
        let currentId := stack.getD (stack.size - 1) candidateId
        stack := stack.pop
        members := members.push currentId
        for targetId in adjacency.getD currentId #[] do
          if !(seen.getD targetId false) then
            seen := seen.set! targetId true
            stack := stack.push targetId
      components := components.push members
  return components

def distancesFrom
    (states : Array State) (adjacency : Array (Array Nat))
    (sourceId : Nat) : Array Nat := Id.run do
  let mut distances := Array.replicate states.size states.size
  let mut queue : Array Nat := #[sourceId]
  distances := distances.set! sourceId 0
  let mut cursor := 0
  while cursor < queue.size do
    let currentId := queue.getD cursor sourceId
    cursor := cursor + 1
    for targetId in adjacency.getD currentId #[] do
      if distances.getD targetId states.size = states.size then
        let currentDistance := distances.getD currentId states.size
        distances := distances.set! targetId (currentDistance + 1)
        queue := queue.push targetId
  return distances

def componentDiameter
    (states : Array State) (adjacency : Array (Array Nat))
    (members : Array Nat) : Nat := Id.run do
  let mut best := 0
  for sourceId in members do
    let distances := distancesFrom states adjacency sourceId
    for targetId in members do
      let distance := distances.getD targetId states.size
      if distance > best then
        best := distance
  return best

def fixedFiberRun
    (states : Array State) (position : CaoPosition) : FixedFiberRun := Id.run do
  let fiberAdjacency := fixedFiberAdjacency states position
  let components :=
    fixedFiberComponents states position fiberAdjacency.adjacency
  let componentSizes := components.map Array.size
  let componentDiameters := components.map fun members => Id.run do
    return componentDiameter states fiberAdjacency.adjacency members
  return {
    position := position
    stateCount := (stateIdsAtCao states position).length
    componentSizes := componentSizes
    componentDiameters := componentDiameters
    directedEdgeCount := fiberAdjacency.directedEdgeCount
    movablePieceCounts := fiberAdjacency.movablePieceCounts
  }

def pieceLabels : List String :=
  Piece.all.map Piece.label

def natArrayJson (values : Array Nat) : String :=
  "[" ++ String.intercalate "," (values.toList.map toString) ++ "]"

def fiberSummaryJson (summary : FixedFiberRun) : String :=
  "{\"position\":[" ++ toString summary.position.1.val ++ "," ++
    toString summary.position.2.val ++
    "],\"stateCount\":" ++ toString summary.stateCount ++
    ",\"componentSizes\":" ++ natArrayJson summary.componentSizes ++
    ",\"componentDiameters\":" ++ natArrayJson summary.componentDiameters ++
    ",\"directedEdgeCount\":" ++ toString summary.directedEdgeCount ++
    ",\"movablePieceCounts\":" ++ natArrayJson summary.movablePieceCounts ++ "}"

def reportJson : String :=
  let summaries := caoPositions.map (fixedFiberRun allShapeStates)
  "{\"meta\":{\"stateModel\":\"allShapeStates\"," ++
    "\"stateCount\":" ++ toString allShapeStates.size ++
    ",\"positionCount\":12,\"pieceLabels\":[" ++
    String.intercalate "," (pieceLabels.map fun label => "\"" ++ label ++ "\"") ++
    "]},\"fibres\":[" ++
    String.intercalate "," (summaries.map fiberSummaryJson) ++ "]}"

def main (args : List String) : IO UInt32 := do
  let output := args.head?.getD "output/cao-guan-fiber-report.json"
  IO.FS.writeFile output reportJson
  IO.println s!"Wrote Cao fibre report for {allShapeStates.size} states to {output}"
  return 0
