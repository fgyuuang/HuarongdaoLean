import Huarongdao.Generic.Transition
import Huarongdao.Generic.Enumeration
import Std.Tactic

namespace SlidingPuzzle

open Huarongdao

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

theorem translated_ne {source target : Pos} {direction : Direction}
    (translatedForward : translated source direction = some target) :
    target ≠ source := by
  cases direction <;> rcases source with ⟨x, y⟩
  · simp [translated] at translatedForward
    rcases translatedForward with ⟨hy, rfl⟩
    intro equal
    have : y - 1 = y := congrArg Pos.y equal
    omega
  · simp [translated] at translatedForward
    subst target
    intro equal
    have : y + 1 = y := congrArg Pos.y equal
    omega
  · simp [translated] at translatedForward
    rcases translatedForward with ⟨hx, rfl⟩
    intro equal
    have : x - 1 = x := congrArg Pos.x equal
    omega
  · simp [translated] at translatedForward
    subst target
    intro equal
    have : x + 1 = x := congrArg Pos.x equal
    omega

theorem valid_positions_size {spec : PuzzleSpec} {state : State}
    (validState : ValidState spec state) :
    state.positions.size = spec.shapes.size := by
  simp [ValidState, valid, inBounds] at validState
  exact validState.1.2.1

theorem setIfInBounds_pos_eq (state : State) {block : Nat}
    (blockInBounds : block < state.positions.size) :
    state.positions.setIfInBounds block (state.pos block) =
      state.positions := by
  apply Array.ext_getElem?
  intro index
  rw [Array.getElem?_setIfInBounds]
  by_cases same : block = index
  · subst index
    simp [blockInBounds, State.pos, Array.getD_eq_getD_getElem?]
  · simp [same]

/-- A successful move from a valid state is undone by moving the same block in
    the reverse direction. -/
theorem tryMove_reverse {spec : PuzzleSpec} {source target : State}
    {block : Nat} {direction : Direction}
    (sourceValid : ValidState spec source)
    (executed :
      tryMove spec source block direction = some target) :
    tryMove spec target block direction.reverse = some source := by
  have blockLt := tryMove_block_lt executed
  have sourceSize := valid_positions_size sourceValid
  have blockSource : block < source.positions.size := by
    omega
  unfold tryMove moveUnchecked at executed
  simp only [blockLt, ↓reduceIte] at executed
  cases translatedMove : translated (source.pos block) direction with
  | none =>
      simp [translatedMove] at executed
  | some moved =>
      simp [translatedMove] at executed
      rcases executed with ⟨_targetValid, rfl⟩
      have movedPos :
          (State.mk
            (source.positions.setIfInBounds block moved)).pos block =
            moved := by
        simp [State.pos, Array.getD_eq_getD_getElem?, blockSource]
      unfold tryMove moveUnchecked
      simp only [
        blockLt,
        ↓reduceIte,
        movedPos,
        translated_reverse translatedMove
      ]
      simp [
        Array.setIfInBounds_setIfInBounds,
        setIfInBounds_pos_eq source blockSource
      ]
      exact sourceValid

theorem step_symm_of_valid {spec : PuzzleSpec}
    {source target : State}
    (sourceValid : ValidState spec source)
    (step : Step spec source target) :
    Step spec target source := by
  rcases step with ⟨action, executed⟩
  exact
    ⟨⟨action.block, action.direction.reverse⟩,
      tryMove_reverse sourceValid executed⟩

theorem step_irrefl (spec : PuzzleSpec) (state : State) :
    ¬ Step spec state state := by
  rintro ⟨action, executed⟩
  have stateValid : ValidState spec state :=
    tryMove_preserves_validity executed
  have blockLt := tryMove_block_lt executed
  have stateSize := valid_positions_size stateValid
  have blockState : action.block < state.positions.size := by
    omega
  unfold tryMove moveUnchecked at executed
  simp only [blockLt, ↓reduceIte] at executed
  cases translatedMove :
      translated (state.pos action.block) action.direction with
  | none =>
      simp [translatedMove] at executed
  | some moved =>
      simp [translatedMove] at executed
      rcases executed with ⟨_candidateValid, restored⟩
      have movedPos :
          (State.mk
            (state.positions.setIfInBounds action.block moved)).pos
              action.block =
            moved := by
        simp [State.pos, Array.getD_eq_getD_getElem?, blockState]
      have equalPosition :=
        congrArg (fun current : State => current.pos action.block) restored
      rw [movedPos] at equalPosition
      exact translated_ne translatedMove equalPosition

end SlidingPuzzle
