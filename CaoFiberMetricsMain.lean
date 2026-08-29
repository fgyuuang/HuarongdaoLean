import Huarongdao.CaoFiberMetrics
import Std.Data.HashMap

open Huarongdao
open Huarongdao.CaoGuanGeometry
open Huarongdao.ClassicFullSpace

structure FiberMetricReport where
  stateCount : Nat
  componentStateCount : Nat
  componentCount : Nat
  fiberSizes : Array Nat
  minDistance : Array (Array Nat)
  hausdorffDistance : Array (Array Nat)
  finite : Bool
  minSymmetric : Bool
  hausdorffSymmetric : Bool
  minTriangle : Bool
  hausdorffTriangle : Bool
  deriving Repr

def metricPositions : Array CaoPosition :=
  ((List.finRange 4).flatMap (fun y =>
    (List.finRange 3).map (fun x => (x, y)))).toArray

def componentRun := componentSummariesOf allShapeStates

def classicComponentId : Nat :=
  match componentSummaries.findIdx? (·.containsClassic) with
  | none => componentSummaries.size
  | some index => index

def stateInClassicComponent (stateId : Nat) : Bool :=
  componentRun.componentOf.getD stateId componentSummaries.size ==
    classicComponentId

def rawStateAt (stateId : Nat) : State :=
  allShapeStates.getD stateId classic

def fiberIds (position : CaoPosition) : Array Nat := Id.run do
  let mut result : Array Nat := #[]
  for stateId in List.range allShapeStates.size do
    if stateInClassicComponent stateId &&
        (rawStateAt stateId).pos .caoCao = position.toPos then
      result := result.push stateId
  return result

def stateNeighbors
    (states : Array State) (index : Std.HashMap Nat Nat)
    (stateId : Nat) : Array Nat := Id.run do
  let source := states.getD stateId classic
  let occupancy := occupancyTable source
  let mut result : Array Nat := #[]
  for piece in Piece.all do
    for direction in Direction.all do
      match locallyLegalMove source occupancy piece direction with
      | none => pure ()
      | some target =>
          match index.get? (placementCode target) with
          | none => pure ()
          | some targetId =>
              if stateInClassicComponent targetId &&
                  !(result.contains targetId) then
                result := result.push targetId
  return result

def stateAdjacency : Array (Array Nat) := Id.run do
  let index := placementIndex allShapeStates
  let mut result : Array (Array Nat) := Array.replicate allShapeStates.size #[]
  for stateId in List.range allShapeStates.size do
    for targetId in stateNeighbors allShapeStates index stateId do
      let sourceNeighbors := result.getD stateId #[]
      if !(sourceNeighbors.contains targetId) then
        result := result.set! stateId (sourceNeighbors.push targetId)
      let targetNeighbors := result.getD targetId #[]
      if !(targetNeighbors.contains stateId) then
        result := result.set! targetId (targetNeighbors.push stateId)
  return result

def infinityDistance (stateCount : Nat) : Nat := stateCount + 1

def distancesFromSources
    (adjacency : Array (Array Nat)) (sources : Array Nat) : Array Nat := Id.run do
  let infinity := infinityDistance allShapeStates.size
  let mut distances := Array.replicate allShapeStates.size infinity
  let mut queue : Array Nat := #[]
  for sourceId in sources do
    if distances.getD sourceId infinity == infinity then
      distances := distances.set! sourceId 0
      queue := queue.push sourceId
  let mut cursor := 0
  while cursor < queue.size do
    let currentId := queue.getD cursor 0
    cursor := cursor + 1
    let currentDistance := distances.getD currentId infinity
    for targetId in adjacency.getD currentId #[] do
      if distances.getD targetId infinity == infinity then
        distances := distances.set! targetId (currentDistance + 1)
        queue := queue.push targetId
  return distances

def distanceMinimum (distances : Array Nat) (targets : Array Nat) : Nat :=
  targets.foldl (fun best targetId =>
    min best (distances.getD targetId (infinityDistance distances.size))) (infinityDistance distances.size)

def distanceMaximum (distances : Array Nat) (sources : Array Nat) : Nat :=
  sources.foldl (fun best sourceId =>
    max best (distances.getD sourceId (infinityDistance distances.size))) 0

def fiberSizeTable : Array Nat :=
  metricPositions.map (fiberIds · |>.size)

def fiberMinDistanceMatrix
    (adjacency : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut rows : Array (Array Nat) := #[]
  for leftIndex in List.range metricPositions.size do
    let leftSources := fiberIds (metricPositions.getD leftIndex (0, 0))
    let distances := distancesFromSources adjacency leftSources
    let mut row : Array Nat := #[]
    for rightIndex in List.range metricPositions.size do
      row := row.push
        (distanceMinimum distances
          (fiberIds (metricPositions.getD rightIndex (0, 0))))
    rows := rows.push row
  return rows

def fiberHausdorffDistanceMatrix
    (adjacency : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut rows : Array (Array Nat) := #[]
  for leftIndex in List.range metricPositions.size do
    let mut row : Array Nat := #[]
    for rightIndex in List.range metricPositions.size do
      let targetIds := fiberIds (metricPositions.getD rightIndex (0, 0))
      let sourceIds := fiberIds (metricPositions.getD leftIndex (0, 0))
      let forwardDistances := distancesFromSources adjacency sourceIds
      let backwardDistances := distancesFromSources adjacency targetIds
      let forward := distanceMaximum forwardDistances targetIds
      let backward := distanceMaximum backwardDistances sourceIds
      row := row.push (max forward backward)
    rows := rows.push row
  return rows

def matrixEntry (matrix : Array (Array Nat))
    (row column : Nat) : Nat :=
  (matrix.getD row #[]).getD column 0

def matrixAll (matrix : Array (Array Nat))
    (predicate : Nat → Nat → Nat → Bool) : Bool := Id.run do
  let mut result := true
  for i in List.range metricPositions.size do
    for j in List.range metricPositions.size do
      if !(predicate i j (matrixEntry matrix i j)) then
        result := false
  return result

def matrixSymmetric (matrix : Array (Array Nat)) : Bool :=
  matrixAll matrix fun i j value => value == matrixEntry matrix j i

def matrixFinite (matrix : Array (Array Nat)) : Bool :=
  matrixAll matrix fun _ _ value => value ≤ allShapeStates.size

def matrixTriangle (matrix : Array (Array Nat)) : Bool := Id.run do
  let mut result := true
  for i in List.range metricPositions.size do
    for j in List.range metricPositions.size do
      for k in List.range metricPositions.size do
        if matrixEntry matrix i k >
            matrixEntry matrix i j + matrixEntry matrix j k then
          result := false
  return result

def buildReport : FiberMetricReport :=
  let run := componentRun
  let adjacency := stateAdjacency
  let minMatrix := fiberMinDistanceMatrix adjacency
  let hausdorffMatrix := fiberHausdorffDistanceMatrix adjacency
  {
    stateCount := allShapeStates.size
    componentStateCount :=
      run.summaries.getD classicComponentId
        ⟨classic, 0, 0, false⟩ |>.stateCount
    componentCount := run.summaries.size
    fiberSizes := fiberSizeTable
    minDistance := minMatrix
    hausdorffDistance := hausdorffMatrix
    finite := matrixFinite hausdorffMatrix
    minSymmetric := matrixSymmetric minMatrix
    hausdorffSymmetric := matrixSymmetric hausdorffMatrix
    minTriangle := matrixTriangle minMatrix
    hausdorffTriangle := matrixTriangle hausdorffMatrix
  }

def jsonNatArray (values : Array Nat) : String :=
  "[" ++ String.intercalate "," (values.toList.map toString) ++ "]"

def jsonMatrix (matrix : Array (Array Nat)) : String :=
  "[" ++ String.intercalate "," (matrix.toList.map jsonNatArray) ++ "]"

def jsonPosition (position : CaoPosition) : String :=
  "[" ++ toString position.1.val ++ "," ++ toString position.2.val ++ "]"

def jsonPositions : String :=
  "[" ++ String.intercalate "," (metricPositions.toList.map jsonPosition) ++ "]"

def reportJson (report : FiberMetricReport) : String :=
  "{\"stateModel\":\"allShapeStates/classic-component\"," ++
    "\"stateCount\":" ++ toString report.stateCount ++
    ",\"componentStateCount\":" ++ toString report.componentStateCount ++
    ",\"componentCount\":" ++ toString report.componentCount ++
    ",\"positions\":" ++ jsonPositions ++
    ",\"fiberSizes\":" ++ jsonNatArray report.fiberSizes ++
    ",\"minimumDistance\":" ++ jsonMatrix report.minDistance ++
    ",\"hausdorffDistance\":" ++ jsonMatrix report.hausdorffDistance ++
    ",\"finite\":" ++ toString report.finite ++
    ",\"minimumSymmetric\":" ++ toString report.minSymmetric ++
    ",\"hausdorffSymmetric\":" ++ toString report.hausdorffSymmetric ++
    ",\"minimumTriangle\":" ++ toString report.minTriangle ++
    ",\"hausdorffTriangle\":" ++ toString report.hausdorffTriangle ++ "}"

def main (args : List String) : IO UInt32 := do
  let report := buildReport
  let output := args.head?.getD "output/cao-fiber-metrics.json"
  IO.FS.writeFile output (reportJson report)
  IO.println s!"Wrote Cao fibre metric report to {output}"
  IO.println s!"states={report.stateCount}, classical component={report.componentStateCount}, components={report.componentCount}"
  IO.println s!"finite={report.finite}, min-symmetric={report.minSymmetric}, Hausdorff-symmetric={report.hausdorffSymmetric}"
  IO.println s!"min-triangle={report.minTriangle}, Hausdorff-triangle={report.hausdorffTriangle}"
  return 0
