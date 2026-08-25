import Huarongdao.Generic.Model

namespace SlidingPuzzle

inductive Path (spec : PuzzleSpec) : State → State → Type where
  | nil (state : State) : Path spec state state
  | cons {source next target : State} (action : Action)
      (executed : tryMove spec source action.block action.direction = some next)
      (tail : Path spec next target) : Path spec source target

namespace Path

def actions : Path spec source target → List Action
  | .nil _ => []
  | .cons action _ tail => action :: tail.actions

def length : Path spec source target → Nat
  | .nil _ => 0
  | .cons _ _ tail => tail.length + 1

theorem runMoves_eq (path : Path spec source target) :
    runMoves spec source path.actions = some target := by
  induction path with
  | nil => rfl
  | cons action executed tail ih => simp [actions, runMoves, executed, ih]

theorem target_valid (path : Path spec source target) (validSource : ValidState spec source) :
    ValidState spec target := by
  induction path with
  | nil => exact validSource
  | cons _ executed _ ih => exact ih (tryMove_preserves_validity executed)

noncomputable def ofRunMoves {spec : PuzzleSpec} {source target : State} {actions : List Action}
    (executed : runMoves spec source actions = some target) : Path spec source target := by
  induction actions generalizing source with
  | nil =>
      simp [runMoves] at executed
      subst target
      exact .nil source
  | cons action rest ih =>
      cases hm : tryMove spec source action.block action.direction with
      | none => simp [runMoves, hm] at executed
      | some next =>
          simp [runMoves, hm] at executed
          exact .cons action hm (ih executed)

end Path

structure Solution (spec : PuzzleSpec) where
  target : State
  path : Path spec spec.initial target
  solved : goalMatches spec target = true

structure CertifiedPlay (spec : PuzzleSpec) where
  actions : List Action
  target : State
  executed : runMoves spec spec.initial actions = some target
  solved : goalMatches spec target = true

namespace CertifiedPlay

def length (play : CertifiedPlay spec) : Nat := play.actions.length

noncomputable def toSolution (play : CertifiedPlay spec) : Solution spec where
  target := play.target
  path := Path.ofRunMoves play.executed
  solved := play.solved

end CertifiedPlay

/-- Executable proposition used at the frontend/search boundary. -/
def Solves (spec : PuzzleSpec) (actions : List Action) : Prop :=
  ∃ target, runMoves spec spec.initial actions = some target ∧ goalMatches spec target = true

theorem solves_iff_nonempty_certified {spec : PuzzleSpec} {actions : List Action} :
    Solves spec actions ↔ ∃ play : CertifiedPlay spec, play.actions = actions := by
  constructor
  · rintro ⟨target, executed, solved⟩
    exact ⟨⟨actions, target, executed, solved⟩, rfl⟩
  · rintro ⟨play, rfl⟩
    exact ⟨play.target, play.executed, play.solved⟩

end SlidingPuzzle
