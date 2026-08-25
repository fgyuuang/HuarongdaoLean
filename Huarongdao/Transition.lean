import Huarongdao.Model

namespace Huarongdao

structure Action where
  piece : Piece
  direction : Direction
  deriving Repr, DecidableEq

def Step (s t : State) : Prop :=
  ∃ action : Action, tryMove s action.piece action.direction = some t

inductive Reachable : State → State → Prop where
  | refl (s : State) : Reachable s s
  | tail {s t u : State} : Step s t → Reachable t u → Reachable s u

theorem tryMove_preserves_validity
    {s t : State} {p : Piece} {d : Direction}
    (h : tryMove s p d = some t) : ValidState t := by
  cases hm : moveUnchecked s p d with
  | none => simp [tryMove, hm] at h
  | some next =>
      by_cases hv : valid next = true
      · simp [tryMove, hm, hv] at h
        cases h
        exact hv
      · simp [tryMove, hm, hv] at h

theorem step_preserves_validity
    {s t : State} (_hs : ValidState s) (h : Step s t) : ValidState t := by
  rcases h with ⟨action, ha⟩
  exact tryMove_preserves_validity ha

theorem reachable_preserves_validity
    {s t : State} (hs : ValidState s) (h : Reachable s t) : ValidState t := by
  induction h with
  | refl => exact hs
  | tail hstep _ ih => exact ih (step_preserves_validity hs hstep)

def runMoves : State → List Action → Option State
  | state, [] => some state
  | state, action :: rest => do
      let next ← tryMove state action.piece action.direction
      runMoves next rest

end Huarongdao
