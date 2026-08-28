import Huarongdao.LocalTopology
import Huarongdao.MirrorQuotient
import Std.Tactic

namespace Huarongdao

/-- The canonical geometry exported as equal-shape quotient node `#1409`. -/
def classicLocal1409 : State := ⟨#[
  ⟨0, 0⟩, ⟨0, 4⟩, ⟨0, 2⟩, ⟨3, 0⟩, ⟨2, 0⟩,
  ⟨3, 2⟩, ⟨3, 4⟩, ⟨1, 3⟩, ⟨2, 4⟩, ⟨1, 2⟩
]⟩

/-- The horizontal mirror of `#1409`; its exported equal-shape id is `#1442`. -/
def classicLocal1442 : State :=
  ⟨#[
    ⟨2, 0⟩, ⟨2, 4⟩, ⟨0, 0⟩, ⟨3, 2⟩, ⟨0, 2⟩,
    ⟨1, 0⟩, ⟨2, 3⟩, ⟨0, 4⟩, ⟨2, 2⟩, ⟨1, 4⟩
  ]⟩

def local1409Actions : List Action := [
  ⟨.maChao, .down⟩,
  ⟨.huangZhong, .left⟩,
  ⟨.soldier2, .right⟩,
  ⟨.soldier3, .up⟩,
  ⟨.soldier4, .right⟩
]

def local1409LinkEdges : List (Action × Action) := [
  (⟨.maChao, .down⟩, ⟨.soldier2, .right⟩),
  (⟨.maChao, .down⟩, ⟨.soldier3, .up⟩),
  (⟨.soldier2, .right⟩, ⟨.soldier4, .right⟩),
  (⟨.soldier3, .up⟩, ⟨.soldier4, .right⟩)
]

def local1409LegalActions : List Action :=
  (legalMoves classicLocal1409).map fun move => ⟨move.1, move.2.1⟩

def checkLocal1409 : Bool :=
  local1409Actions.all fun action => (tryAction classicLocal1409 action).isSome &&
  local1409LinkEdges.all fun pair =>
    checkActionsCommuteAt classicLocal1409 pair.1 pair.2

def checkLocal1409IsolatedAction : Bool :=
  let isolated : Action := ⟨.huangZhong, .left⟩
  [⟨.maChao, .down⟩, ⟨.soldier2, .right⟩,
    ⟨.soldier3, .up⟩, ⟨.soldier4, .right⟩].all fun action =>
      !checkActionsCommuteAt classicLocal1409 isolated action

def checkLocal1409NoCommutingTriple : Bool :=
  local1409Actions.all fun a =>
    local1409Actions.all fun b =>
      local1409Actions.all fun c =>
        a == b || a == c || b == c ||
          !(checkActionsCommuteAt classicLocal1409 a b &&
            checkActionsCommuteAt classicLocal1409 a c &&
            checkActionsCommuteAt classicLocal1409 b c)

/-- Kernel-evaluated witness that the selected link contains `C4 ⊔ {point}`. -/
theorem classicLocal1409_checked : checkLocal1409 = true := by
  set_option maxHeartbeats 0 in
  native_decide

/-- There are exactly five legal labelled moves at the sample state. -/
theorem classicLocal1409_legal_actions :
    local1409LegalActions = local1409Actions := by
  native_decide

/-- The four displayed pairs are genuine semantic link edges. -/
theorem classicLocal1409_link_cycle :
    LinkEdge classicLocal1409 ⟨.maChao, .down⟩ ⟨.soldier2, .right⟩ ∧
    LinkEdge classicLocal1409 ⟨.maChao, .down⟩ ⟨.soldier3, .up⟩ ∧
    LinkEdge classicLocal1409 ⟨.soldier2, .right⟩ ⟨.soldier4, .right⟩ ∧
    LinkEdge classicLocal1409 ⟨.soldier3, .up⟩ ⟨.soldier4, .right⟩ := by
  native_decide

/-- The fifth legal move is isolated from the four-cycle in the action link. -/
theorem classicLocal1409_huangZhong_isolated :
    ¬ LinkEdge classicLocal1409 ⟨.huangZhong, .left⟩ ⟨.maChao, .down⟩ ∧
    ¬ LinkEdge classicLocal1409 ⟨.huangZhong, .left⟩ ⟨.soldier2, .right⟩ ∧
    ¬ LinkEdge classicLocal1409 ⟨.huangZhong, .left⟩ ⟨.soldier3, .up⟩ ∧
    ¬ LinkEdge classicLocal1409 ⟨.huangZhong, .left⟩ ⟨.soldier4, .right⟩ := by
  native_decide

/-- The two diagonals of the four action vertices do not commute. -/
theorem classicLocal1409_link_diagonals_absent :
    ¬ LinkEdge classicLocal1409 ⟨.maChao, .down⟩ ⟨.soldier4, .right⟩ ∧
    ¬ LinkEdge classicLocal1409 ⟨.soldier2, .right⟩ ⟨.soldier3, .up⟩ := by
  native_decide

/-- The two possible cycle triples are not pairwise commuting. -/
theorem classicLocal1409_cycle_triples_not_pairwise :
    ¬ PairwiseCommuteAt classicLocal1409
      [⟨.maChao, .down⟩, ⟨.soldier2, .right⟩, ⟨.soldier4, .right⟩] ∧
    ¬ PairwiseCommuteAt classicLocal1409
      [⟨.maChao, .down⟩, ⟨.soldier3, .up⟩, ⟨.soldier4, .right⟩] := by
  native_decide

/-- Exhaustive kernel check: no three distinct legal actions commute pairwise. -/
theorem classicLocal1409_no_commuting_triple_checked :
    checkLocal1409NoCommutingTriple = true := by
  native_decide

/-- Huang Zhong's left move is the isolated vertex in the selected action link. -/
theorem classicLocal1409_isolated_checked :
    checkLocal1409IsolatedAction = true := by
  set_option maxHeartbeats 0 in
  native_decide

/-- The sample is paired with exported node `#1442` by horizontal reflection. -/
theorem classicLocal1409_mirror_key :
    (mirrorState classicLocal1409).key = classicLocal1442.key := by
  set_option maxHeartbeats 0 in
  native_decide

end Huarongdao
