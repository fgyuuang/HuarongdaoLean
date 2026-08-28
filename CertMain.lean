import Huarongdao.CorridorExport

open Huarongdao

def main : IO UInt32 := do
  IO.println "Building quotient graph certificate in Lean..."
  let graph := enumerate classic
  let mirrorGraph := enumerateMirror
  let corridor := buildCorridorExport mirrorGraph
  let emptyMirrorEdgeComplete :=
    checkMirrorEdgesComplete { mirrorGraph with edges := #[] }
  let mirrorMissingReverse :=
    checkMirrorReversible { mirrorGraph with edges := mirrorGraph.edges.pop }
  let corridorMissingReverse :=
    checkCorridorExport { mirrorGraph with edges := mirrorGraph.edges }
      { corridor with edges := corridor.edges.pop }
  IO.println s!"states={graph.states.size}, edges={graph.edges.size}"
  IO.println
    s!"mirror states={mirrorGraph.states.size}, edges={mirrorGraph.edges.size}"
  IO.println
    s!"mirror directed adjacencies={directedAdjacencyCount mirrorGraph}, parallel edges={mirrorGraph.edges.size - directedAdjacencyCount mirrorGraph}"
  let edgeSound := checkEdges graph
  let closed := checkClosedFast graph
  let unique := checkUniqueKeys graph
  let distances := checkDistances graph
  let lower116 := checkGoalLowerBound graph 116
  let goal116 := checkGoalAt graph 116
  let kernelReady := checkQuotientLowerBound graph classic 116
  let mirrorEdgeSound := checkMirrorEdges mirrorGraph
  let mirrorEdgeComplete := checkMirrorEdgesComplete mirrorGraph
  let mirrorValid := checkMirrorValidStates mirrorGraph
  let mirrorClosed := checkMirrorClosed mirrorGraph
  let mirrorLower116 :=
    checkMirrorGoalLowerBound mirrorGraph 116
  let mirrorKernelReady :=
    checkMirrorQuotientLowerBound mirrorGraph classic 116
  let corridorReady := checkCorridorExport mirrorGraph corridor
  IO.println s!"all quotient edges sound: {edgeSound}"
  IO.println s!"all legal successors represented: {closed}"
  IO.println s!"canonical representatives unique: {unique}"
  IO.println s!"distance constraints valid: {distances}"
  IO.println s!"all goals have distance >= 116: {lower116}"
  IO.println s!"a goal exists at distance 116: {goal116}"
  IO.println s!"kernel certificate conditions valid: {kernelReady}"
  IO.println s!"all mirror quotient edges sound: {mirrorEdgeSound}"
  IO.println s!"all mirror legal moves have stored edges: {mirrorEdgeComplete}"
  IO.println
    s!"empty mirror edge set rejected: {!emptyMirrorEdgeComplete}"
  IO.println
    s!"missing corridor reverse rejected: {!corridorMissingReverse}"
  IO.println
    s!"missing parent reverse rejected: {!mirrorMissingReverse}"
  IO.println
    s!"corridor checks directed adjacencies, not parallel action labels: {decide (directedAdjacencyCount mirrorGraph < mirrorGraph.edges.size)}"
  IO.println s!"all mirror representatives valid: {mirrorValid}"
  IO.println s!"all mirror successors represented: {mirrorClosed}"
  IO.println s!"all mirror goals have distance >= 116: {mirrorLower116}"
  IO.println
    s!"mirror kernel certificate conditions valid: {mirrorKernelReady}"
  IO.println s!"corridor segmentation certificate valid: {corridorReady}"
  return if edgeSound && closed && unique && distances &&
      lower116 && goal116 && kernelReady &&
      mirrorEdgeSound && mirrorEdgeComplete && mirrorValid && mirrorClosed &&
      mirrorLower116 && mirrorKernelReady && corridorReady &&
      !emptyMirrorEdgeComplete && !mirrorMissingReverse &&
      !corridorMissingReverse then
    0
  else
    1
