import Huarongdao.Transition
import Std.Tactic

namespace Huarongdao

namespace Direction

/-- The inverse direction of a primitive sliding-block move. -/
def reverse : Direction → Direction
  | .up => .down
  | .down => .up
  | .left => .right
  | .right => .left

@[simp] theorem reverse_reverse (direction : Direction) :
    direction.reverse.reverse = direction := by
  cases direction <;> rfl

end Direction

theorem translated_reverse {source target : Pos} {direction : Direction}
    (translatedForward : translated source direction = some target) :
    translated target direction.reverse = some source := by
  cases direction <;> rcases source with ⟨x, y⟩
  · simp [translated] at translatedForward
    rcases translatedForward with ⟨hy, rfl⟩
    simp [Direction.reverse, translated]
    omega
  · simp [translated] at translatedForward
    subst target
    simp [Direction.reverse, translated]
  · simp [translated] at translatedForward
    rcases translatedForward with ⟨hx, rfl⟩
    simp [Direction.reverse, translated]
    omega
  · simp [translated] at translatedForward
    subst target
    simp [Direction.reverse, translated]

theorem state_ofFn_pos_congr {f g : Piece → Pos} (h : ∀ p, f p = g p) :
    State.ofFn f = State.ofFn g := by
  unfold State.ofFn
  apply congrArg State.mk
  apply Array.ext
  · rfl
  · intro i hi1 hi2
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by
      simp at hi1 hi2
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [h]

/-- A valid canonical state is exactly the array assembled from its piece
    positions. -/
theorem state_ofFn_eq_self (s : State) (hs : ValidState s) :
    State.ofFn (fun p => s.pos p) = s := by
  unfold ValidState valid inBounds at hs
  simp only [Bool.and_eq_true] at hs
  rcases hs with ⟨hs, _⟩
  have hsize : s.positions.size = 10 := by
    simpa [Piece.all] using hs.1
  cases s with | mk positions =>
  unfold State.ofFn
  apply congrArg State.mk
  apply Array.ext
  · simp [hsize]
  · intro i hi1 hi2
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by
      simp at hi1 hi2
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [State.pos, Piece.index]
      rw [Array.getElem?_eq_getElem hi2]
      rfl

theorem moveUnchecked_reverse {s t : State} {p : Piece} {d : Direction}
    (h : moveUnchecked s p d = some t) :
    moveUnchecked t p d.reverse =
      some (State.ofFn (fun q => s.pos q)) := by
  unfold moveUnchecked at h
  cases hm : translated (s.pos p) d with
  | none => simp [hm] at h
  | some movedPos =>
      simp [hm] at h
      subst t
      unfold moveUnchecked
      have tp :
          (State.ofFn
            (fun q => if q = p then movedPos else s.pos q)).pos p =
            movedPos := by
        simp
      rw [tp, translated_reverse hm]
      simp
      apply state_ofFn_pos_congr
      intro q
      by_cases hq : q = p
      · subst q; simp
      · simp [hq]

/-- A successful move from a valid state is undone by moving the same piece
    in the reverse direction. -/
theorem tryMove_reverse {s t : State} {p : Piece} {d : Direction}
    (sourceValid : ValidState s)
    (executed : tryMove s p d = some t) :
    tryMove t p d.reverse = some s := by
  unfold tryMove at executed
  cases hm : moveUnchecked s p d with
  | none => simp [hm] at executed
  | some candidate =>
      by_cases hv : valid candidate = true
      · simp [hm, hv] at executed
        subst t
        unfold tryMove
        have hrev := moveUnchecked_reverse (p := p) (d := d) hm
        rw [hrev]
        simp
        have hvalid : valid (State.ofFn (fun q => s.pos q)) = true := by
          rw [state_ofFn_eq_self s sourceValid]
          exact sourceValid
        rw [hvalid]
        simp [state_ofFn_eq_self s sourceValid]
      · simp [hm, hv] at executed

theorem step_symm_of_valid {s t : State}
    (sourceValid : ValidState s) (step : Step s t) :
    Step t s := by
  rcases step with ⟨action, executed⟩
  exact ⟨⟨action.piece, action.direction.reverse⟩,
    tryMove_reverse sourceValid executed⟩

end Huarongdao
