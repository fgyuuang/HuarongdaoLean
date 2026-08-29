import Huarongdao.GuanYuYieldBridge
import Std.Data.HashSet
import Std.Tactic

namespace Huarongdao
namespace GuanYuYieldTheory

def yieldAvoidanceLegalMoves (source : State) :
    List (Piece × Direction × State) :=
  (legalMoves source).filter fun move =>
    !guanYuYieldFlag source ⟨move.1, move.2.1⟩ move.2.2

/-!
## A finite certificate extracted from the avoidance search

`avoidYieldBfs` only exposes its final `none` result.  The definitions below
replay the same finite search while retaining its queue.  The two executable
checks then turn that queue into the semantic certificate required by
`FiniteYieldAvoidanceCertificate`.
-/

def avoidYieldQueue : Array State := Id.run do
  let mut queue : Array State := #[classic]
  let mut known : Std.HashSet String := {}
  known := known.insert classic.key
  let mut cursor := 0
  while cursor < queue.size do
    let source := queue.getD cursor classic
    for move in yieldAvoidanceLegalMoves source do
      let target := move.2.2
      if !known.contains target.key then
        known := known.insert target.key
        queue := queue.push target
    cursor := cursor + 1
  return queue

def avoidYieldQueueNoGoal : Bool :=
  avoidYieldQueue.all fun state => !goal state

def avoidYieldQueueClosed : Bool :=
  (List.range avoidYieldQueue.size).all fun index =>
    let source := avoidYieldQueue.getD index classic
    (yieldAvoidanceLegalMoves source).all fun move =>
      avoidYieldQueue.any fun representative =>
        decide (SameShape move.2.2 representative)

set_option maxHeartbeats 0 in
theorem avoidYieldQueue_no_goal : avoidYieldQueueNoGoal = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem avoidYieldQueue_closed : avoidYieldQueueClosed = true := by
  native_decide

private theorem avoidYieldQueue_member_closed
    {index : Nat} (indexLt : index < avoidYieldQueue.size)
    (checked : avoidYieldQueueClosed = true)
    {piece : Piece} {direction : Direction} {target : State}
    (executed :
      tryMove (avoidYieldQueue.getD index classic) piece direction =
        some target)
    (notYield :
      ¬ GuanYuYield
        (avoidYieldQueue.getD index classic)
        ⟨piece, direction⟩ target) :
    ∃ next : Fin avoidYieldQueue.size,
      SameShape target (avoidYieldQueue.getD next.1 classic) := by
  have moveMember :
      (piece, direction, target) ∈
        yieldAvoidanceLegalMoves (avoidYieldQueue.getD index classic) := by
    have legal : (piece, direction, target) ∈
        legalMoves (avoidYieldQueue.getD index classic) :=
      legalMoves_complete executed
    unfold yieldAvoidanceLegalMoves
    simp only [List.mem_filter]
    refine ⟨legal, ?_⟩
    by_cases flag : guanYuYieldFlag
        (avoidYieldQueue.getD index classic) ⟨piece, direction⟩ target = true
    · exact False.elim (notYield (by
        have flag' := flag
        unfold guanYuYieldFlag at flag'
        unfold GuanYuYield
        simp only [Bool.and_eq_true, beq_iff_eq] at flag'
        exact ⟨flag'.1.1, flag'.1.2, of_decide_eq_true flag'.2⟩))
    · have flagFalse : guanYuYieldFlag
          (avoidYieldQueue.getD index classic) ⟨piece, direction⟩ target =
          false :=
        Bool.eq_false_of_not_eq_true flag
      rw [Bool.not_eq_true_eq_eq_false]
      exact flagFalse
  have sourceChecked :
      (yieldAvoidanceLegalMoves
        (avoidYieldQueue.getD index classic)).all (fun move =>
          avoidYieldQueue.any fun representative =>
            decide (SameShape move.2.2 representative)) := by
    unfold avoidYieldQueueClosed at checked
    rw [List.all_eq_true] at checked
    exact checked index (List.mem_range.mpr indexLt)
  have targetChecked :=
    (List.all_eq_true.mp sourceChecked) (piece, direction, target) moveMember
  rw [Array.any_eq_true] at targetChecked
  rcases targetChecked with ⟨next, nextLt, same⟩
  exact ⟨⟨next, nextLt⟩, by
    simpa [Array.getD, nextLt] using (of_decide_eq_true same)⟩

private theorem avoidYieldQueue_goal_excluded :
    ∀ {index : Fin avoidYieldQueue.size},
      goal (avoidYieldQueue.getD index.1 classic) = true → False := by
  intro index goalTrue
  have checked := Array.all_eq_true.mp avoidYieldQueue_no_goal index index.2
  have checked' :
      goal (avoidYieldQueue.getD index.1 classic) = false := by
    simpa [Array.getD, index.2] using checked
  rw [goalTrue] at checked'
  cases checked'

def avoidYieldQueueAllValid : Bool :=
  avoidYieldQueue.all valid

set_option maxHeartbeats 0 in
private theorem avoidYieldQueue_all_valid :
    avoidYieldQueueAllValid = true := by
  native_decide

private theorem avoidYieldQueue_valid
    (index : Fin avoidYieldQueue.size) :
    ValidState (avoidYieldQueue.getD index.1 classic) := by
  have checked :
      (avoidYieldQueue.toList).all valid = true := by
    simpa [avoidYieldQueueAllValid] using avoidYieldQueue_all_valid
  have member :
      avoidYieldQueue.getD index.1 classic ∈ avoidYieldQueue.toList := by
    have valueEq :
        avoidYieldQueue.getD index.1 classic =
          avoidYieldQueue[index.1] := by
      simp [Array.getD, index.2]
    rw [valueEq]
    exact Array.getElem_mem_toList index.2
  have value := List.all_eq_true.mp checked _ member
  simpa [ValidState] using value

private theorem avoidYieldQueue_zero :
    avoidYieldQueue.getD 0 classic = classic := by
  native_decide

def avoidYieldFiniteCertificate :
    FiniteYieldAvoidanceCertificate classic where
  Node := Fin avoidYieldQueue.size
  represents state index :=
    ValidState state ∧
      SameShape state (avoidYieldQueue.getD index.1 classic)
  startNode := ⟨0, by native_decide⟩
  startRepresented := by
    constructor
    · exact classic_valid
    · change SameShape classic (avoidYieldQueue.getD 0 classic)
      rw [avoidYieldQueue_zero]
      exact sameShape_refl classic
  inside _ := true
  startInside := rfl
  simulateNoYield := by
    intro source target node action represented executed notYield
    rcases represented with ⟨sourceValid, sourceSame⟩
    have representativeValid := avoidYieldQueue_valid node
    let relabeling :=
      sameShapeRelabeling sourceValid representativeValid sourceSame
    have sourceEq :
        relabelState relabeling source =
          avoidYieldQueue.getD node.1 classic :=
      sameShapeRelabeling_eq sourceValid representativeValid sourceSame
    let representativeAction := relabelAction relabeling action
    let representativeTarget := relabelState relabeling target
    have transported :
        tryMove (relabelState relabeling source)
            representativeAction.piece representativeAction.direction =
          some representativeTarget :=
      tryMove_relabel_some relabeling executed
    have representativeStep :
      tryMove (avoidYieldQueue.getD node.1 classic)
            representativeAction.piece representativeAction.direction =
          some representativeTarget := by
      rw [← sourceEq]
      exact transported
    have representativeNotYield :
        ¬ GuanYuYield
          (avoidYieldQueue.getD node.1 classic)
          representativeAction representativeTarget := by
      intro contradiction
      apply notYield
      have restored :=
        (GuanYuYield.relabel_iff relabeling sourceValid
          (tryMove_preserves_validity executed)).mpr
          (by
            simpa [representativeAction, representativeTarget, ← sourceEq] using
              contradiction)
      exact restored
    obtain ⟨next, nextSame⟩ :=
      avoidYieldQueue_member_closed node.2 avoidYieldQueue_closed
        representativeStep representativeNotYield
    have targetValid : ValidState target :=
      tryMove_preserves_validity executed
    refine ⟨next, rfl, ?_⟩
    constructor
    · exact targetValid
    · exact sameShape_trans
        (sameShape_symm (relabel_sameShape relabeling target))
        nextSame
  goalExcluded := by
    intro target node represented _inside goalTrue
    have goalAt :
        goal (avoidYieldQueue.getD node.1 classic) = true := by
      rw [← sameShape_goal represented.2]
      exact goalTrue
    exact avoidYieldQueue_goal_excluded (index := node) goalAt

theorem classic_solution_uses_guanYu_yield
    (solution : Solution classic) :
    solution.path.UsesTransition GuanYuYield :=
  classic_solution_uses_guanYu_yield_of_finite_certificate
    avoidYieldFiniteCertificate solution

end GuanYuYieldTheory
end Huarongdao
