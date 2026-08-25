import Huarongdao.Transition

namespace Huarongdao

/-- A proof-carrying path: every constructor stores one checked move. -/
inductive Path : State → State → Type where
  | nil (s : State) : Path s s
  | cons {s u t : State} (action : Action)
      (step : tryMove s action.piece action.direction = some u)
      (tail : Path u t) : Path s t

namespace Path

def actions : {s t : State} → Path s t → List Action
  | _, _, .nil _ => []
  | _, _, .cons action _ tail => action :: tail.actions

def length : Path s t → Nat
  | .nil _ => 0
  | .cons _ _ tail => tail.length + 1

theorem actions_length (path : Path s t) : path.actions.length = path.length := by
  induction path with
  | nil => rfl
  | cons _ _ _ ih => simp [actions, length, ih]

theorem runMoves_eq (path : Path s t) : runMoves s path.actions = some t := by
  induction path with
  | nil => rfl
  | cons action step tail ih => simp [actions, runMoves, step, ih]

/-- Turn a successful executable run into a proof-carrying path. -/
noncomputable def ofRunMoves {s t : State} {as : List Action}
    (h : runMoves s as = some t) : Path s t := by
  induction as generalizing s with
  | nil =>
      simp [runMoves] at h
      subst t
      exact .nil s
  | cons action rest ih =>
      cases hm : tryMove s action.piece action.direction with
      | none => simp [runMoves, hm] at h
      | some u =>
          simp [runMoves, hm] at h
          exact .cons action hm (ih h)

theorem toReachable (path : Path s t) : Reachable s t := by
  induction path with
  | nil => exact .refl _
  | cons action step _ ih =>
      exact .tail ⟨action, step⟩ ih

theorem target_valid (path : Path s t) (hs : ValidState s) : ValidState t :=
  reachable_preserves_validity hs path.toReachable

end Path

/-- Completing the puzzle is literally an inhabitant carrying a path and goal proof. -/
structure Solution (start : State) where
  target : State
  path : Path start target
  solved : goal target = true

namespace Solution

def actions (solution : Solution start) : List Action := solution.path.actions

def length (solution : Solution start) : Nat := solution.path.length

/-- A solution is minimal when no other proof-carrying solution is shorter. -/
def Minimal (solution : Solution start) : Prop :=
  ∀ other : Solution start, solution.length ≤ other.length

/-- Executable completion predicate: an action list itself is a proof witness. -/
def Solves (start : State) (actions : List Action) : Prop :=
  ∃ target, runMoves start actions = some target ∧ goal target = true

/-- Every executable completion constructs an inhabitant of Solution. -/
theorem solves_to_solution {start : State} {actions : List Action}
    (h : Solves start actions) : Nonempty (Solution start) := by
  rcases h with ⟨target, hrun, hgoal⟩
  exact ⟨⟨target, Path.ofRunMoves hrun, hgoal⟩⟩

theorem runMoves_eq (solution : Solution start) :
    runMoves start solution.actions = some solution.target :=
  solution.path.runMoves_eq

theorem toSolves (solution : Solution start) : Solves start solution.actions :=
  ⟨solution.target, solution.runMoves_eq, solution.solved⟩

theorem reachable_goal (solution : Solution start) :
    Reachable start solution.target ∧ goal solution.target = true :=
  ⟨solution.path.toReachable, solution.solved⟩

theorem target_valid (solution : Solution start) (hs : ValidState start) :
    ValidState solution.target :=
  solution.path.target_valid hs

end Solution

end Huarongdao
