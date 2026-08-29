import Huarongdao.GuanYuYield
import Huarongdao.ClassicFullSpace
import Std.Data.HashSet
import Std.Data.HashMap

open Huarongdao
open Huarongdao.GuanYuYieldTheory
open Huarongdao.ClassicFullSpace

structure YieldEvent where
  index : Nat
  action : Action
  source : State
  target : State
  before : Nat
  after : Nat
  deriving Repr

def scanYieldEvents : State → List Action → Nat → List YieldEvent
  | _, [], _ => []
  | source, action :: rest, index =>
      match tryMove source action.piece action.direction with
      | none => []
      | some target =>
          let next := scanYieldEvents target rest (index + 1)
          if guanYuYieldFlag source action target then
            { index := index
              action := action
              source := source
              target := target
              before := guanYuCaoSweepBlockage source
              after := guanYuCaoSweepBlockage target } :: next
          else
            next

def classicYieldEvents : List YieldEvent :=
  scanYieldEvents classic classic116Actions 0

def legalMovesWithoutYield (source : State) :
    List (Piece × Direction × State) :=
  (legalMoves source).filter fun move =>
    !guanYuYieldFlag source ⟨move.1, move.2.1⟩ move.2.2

def avoidYieldBfs : Option (State × List Action) := Id.run do
  let mut queue : Array (State × List Action) := #[(classic, [])]
  let mut known : Std.HashSet String := {}
  known := known.insert classic.key
  let mut cursor := 0
  while cursor < queue.size do
    let current := queue.getD cursor (classic, [])
    let source := current.1
    let actions := current.2
    if goal source then
      return some current
    for move in legalMovesWithoutYield source do
      let target := move.2.2
      if !known.contains target.key then
        known := known.insert target.key
        queue := queue.push
          (target, actions ++ [⟨move.1, move.2.1⟩])
    cursor := cursor + 1
  return none

def corridorOpenBool (state : State) : Bool :=
  match tryMove state .caoCao .down with
  | some _ => true
  | none => false

def jointRawKey (state : State) : String :=
  toString (state.pos .caoCao).code ++ ";" ++
    toString (state.pos .guanYu).code

/--
Search the complete geometric placement enumeration for two states with the
same Cao Cao/Guan Yu coordinates but different corridor status.
-/
def findJointObservationCollision : Option (State × State) := Id.run do
  let mut seen : Std.HashMap String (State × Bool) := {}
  for state in allShapeStates do
    let key := jointRawKey state
    let isOpen := corridorOpenBool state
    match seen.get? key with
    | some (previous, previousOpen) =>
        if previousOpen != isOpen then
          return some (previous, state)
    | none =>
        seen := seen.insert key (state, isOpen)
  return none

/-!
This is the checked finite computation behind the avoidance claim.  It is
intentionally kept next to the executable BFS: the theorem certifies the
returned finite search result, while `YieldAvoidanceCertificate` in the
library is the semantic interface still needed to lift that result to every
labelled path.
-/
set_option maxHeartbeats 0 in
theorem avoidYieldBfs_none : avoidYieldBfs = none := by
  native_decide

def actionLabel (action : Action) : String :=
  action.piece.label ++ action.direction.label

def yieldEventSummary (event : YieldEvent) : String :=
  toString event.index ++ ":" ++ actionLabel event.action ++
    "(" ++ toString event.before ++ "->" ++ toString event.after ++ ")"

def main (_args : List String) : IO UInt32 := do
  IO.println s!"classic yield events: {classicYieldEvents.map yieldEventSummary}"
  match avoidYieldBfs with
  | none =>
      IO.println "avoid-yield quotient BFS: no goal found"
  | some result =>
      IO.println s!"avoid-yield quotient BFS: goal found in {result.2.length} steps"
      IO.println s!"actions: {result.2.map actionLabel}"
  match findJointObservationCollision with
  | none =>
      IO.println "joint observation collision: none found"
  | some (left, right) =>
      IO.println s!"joint observation collision key: {jointRawKey left}"
      IO.println s!"left corridor open: {corridorOpenBool left}, state: {repr left}"
      IO.println s!"right corridor open: {corridorOpenBool right}, state: {repr right}"
  return 0
