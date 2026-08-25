import Huarongdao.Generic.Model

namespace SlidingPuzzle

open Huarongdao Direction

theorem Direction.mem_all (direction : Direction) : direction ∈ Direction.all := by
  cases direction <;> simp [Direction.all]

theorem tryMove_block_lt {spec : PuzzleSpec} {state next : State}
    {block : Nat} {direction : Direction}
    (executed : tryMove spec state block direction = some next) :
    block < spec.shapes.size := by
  unfold tryMove moveUnchecked at executed
  by_cases h : block < spec.shapes.size
  · exact h
  · simp [h] at executed

/-- Exact specification of the generic legal move enumerator. -/
theorem mem_legalMoves_iff {spec : PuzzleSpec} {state next : State}
    {action : Action} :
    (action, next) ∈ legalMoves spec state ↔
      tryMove spec state action.block action.direction = some next := by
  cases action with
  | mk block direction =>
    constructor
    · intro member
      simp [legalMoves, List.mem_flatMap, List.mem_filterMap] at member
      rcases member with ⟨foundBlock, _hb, foundDirection, _hd, executed, hblock, hdirection⟩
      subst foundBlock
      subst foundDirection
      exact executed
    · intro executed
      have blockLt := tryMove_block_lt executed
      simp [legalMoves, List.mem_flatMap, List.mem_filterMap, blockIds,
        blockLt, executed, Direction.mem_all]

theorem legalMoves_sound {spec : PuzzleSpec} {state next : State} {action : Action}
    (member : (action, next) ∈ legalMoves spec state) :
    tryMove spec state action.block action.direction = some next :=
  mem_legalMoves_iff.mp member

theorem legalMoves_complete {spec : PuzzleSpec} {state next : State} {action : Action}
    (executed : tryMove spec state action.block action.direction = some next) :
    (action, next) ∈ legalMoves spec state :=
  mem_legalMoves_iff.mpr executed

end SlidingPuzzle
