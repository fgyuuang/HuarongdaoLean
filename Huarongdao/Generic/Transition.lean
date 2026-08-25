import Huarongdao.Generic.Paths

namespace SlidingPuzzle

def Step (spec : PuzzleSpec) (source target : State) : Prop :=
  ∃ action : Action, tryMove spec source action.block action.direction = some target

inductive Reachable (spec : PuzzleSpec) : State → State → Prop where
  | refl (state : State) : Reachable spec state state
  | tail {source next target : State} :
      Step spec source next → Reachable spec next target → Reachable spec source target

theorem step_preserves_validity {spec : PuzzleSpec} {source target : State}
    (_sourceValid : ValidState spec source) (step : Step spec source target) :
    ValidState spec target := by
  rcases step with ⟨action, executed⟩
  exact tryMove_preserves_validity executed

theorem reachable_preserves_validity {spec : PuzzleSpec} {source target : State}
    (sourceValid : ValidState spec source) (reachable : Reachable spec source target) :
    ValidState spec target := by
  induction reachable with
  | refl => exact sourceValid
  | tail step _ ih => exact ih (step_preserves_validity sourceValid step)

theorem Path.toReachable (path : Path spec source target) : Reachable spec source target := by
  induction path with
  | nil => exact .refl _
  | cons action executed _ ih => exact .tail ⟨action, executed⟩ ih

theorem Solution.target_reachable (solution : Solution spec) :
    Reachable spec spec.initial solution.target := solution.path.toReachable

end SlidingPuzzle
