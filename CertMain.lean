import Huarongdao

open Huarongdao

def main : IO UInt32 := do
  IO.println "Building quotient graph certificate in Lean..."
  let graph := enumerate classic
  IO.println s!"states={graph.states.size}, edges={graph.edges.size}"
  let edgeSound := checkEdges graph
  let closed := checkClosedFast graph
  let unique := checkUniqueKeys graph
  let distances := checkDistances graph
  let lower116 := checkGoalLowerBound graph 116
  let goal116 := checkGoalAt graph 116
  let kernelReady := checkQuotientLowerBound graph classic 116
  IO.println s!"all quotient edges sound: {edgeSound}"
  IO.println s!"all legal successors represented: {closed}"
  IO.println s!"canonical representatives unique: {unique}"
  IO.println s!"distance constraints valid: {distances}"
  IO.println s!"all goals have distance >= 116: {lower116}"
  IO.println s!"a goal exists at distance 116: {goal116}"
  IO.println s!"kernel certificate conditions valid: {kernelReady}"
  return if edgeSound && closed && unique && distances &&
      lower116 && goal116 && kernelReady then
    0
  else
    1
