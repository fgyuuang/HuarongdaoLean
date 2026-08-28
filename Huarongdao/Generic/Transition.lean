import Huarongdao.Generic.StateSpace

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

/-- Compatibility reachability embeds into canonical task reachability. -/
theorem Reachable.toTaskReachable
    (reachable : Reachable spec source target) :
    (stateSpaceTask spec).Reachable source target := by
  induction reachable with
  | refl state => exact ⟨.nil state⟩
  | tail step _ ih =>
      rcases step with ⟨action, executed⟩
      rcases ih with ⟨tail⟩
      exact ⟨.cons action executed tail⟩

/-- Canonical task reachability maps back to the compatibility predicate. -/
theorem reachableOfTaskReachable
    (reachable : (stateSpaceTask spec).Reachable source target) :
    Reachable spec source target := by
  rcases reachable with ⟨walk⟩
  exact (pathOfTaskWalk walk).toReachable

theorem reachable_iff_taskReachable :
    Reachable spec source target ↔
      (stateSpaceTask spec).Reachable source target :=
  ⟨Reachable.toTaskReachable, reachableOfTaskReachable⟩

theorem Path.toTaskReachable (path : Path spec source target) :
    (stateSpaceTask spec).Reachable source target :=
  ⟨taskWalkOfPath path⟩

theorem Solution.target_reachable (solution : Solution spec) :
    Reachable spec spec.initial solution.target := solution.path.toReachable

theorem Solution.target_taskReachable (solution : Solution spec) :
    (stateSpaceTask spec).Reachable spec.initial solution.target :=
  solution.path.toTaskReachable

end SlidingPuzzle
