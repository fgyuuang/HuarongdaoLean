import Huarongdao.Paths

namespace Huarongdao

/-- The player's action list together with executable and goal certificates. -/
structure CertifiedPlay (start : State) where
  actions : List Action
  target : State
  executed : runMoves start actions = some target
  solved : goal target = true

namespace CertifiedPlay

def length (play : CertifiedPlay start) : Nat := play.actions.length

def Minimal (play : CertifiedPlay start) : Prop :=
  ∀ other : CertifiedPlay start, play.length ≤ other.length

noncomputable def toSolution (play : CertifiedPlay start) : Solution start where
  target := play.target
  path := Path.ofRunMoves play.executed
  solved := play.solved

theorem toSolves (play : CertifiedPlay start) : Solution.Solves start play.actions :=
  ⟨play.target, play.executed, play.solved⟩

theorem target_valid (play : CertifiedPlay start) (hs : ValidState start) :
    ValidState play.target :=
  (play.toSolution).target_valid hs

end CertifiedPlay

/-- An automorphism of the executable transition system. -/
structure GameSymmetry where
  mapState : State → State
  mapAction : Action → Action
  involutiveState : ∀ s, mapState (mapState s) = s
  involutiveAction : ∀ a, mapAction (mapAction a) = a
  move_commutes : ∀ s a,
    tryMove (mapState s) (mapAction a).piece (mapAction a).direction =
      (tryMove s a.piece a.direction).map mapState
  goal_invariant : ∀ s, goal (mapState s) = goal s

namespace GameSymmetry

def mapPath (symmetry : GameSymmetry) : {s t : State} →
    Path s t → Path (symmetry.mapState s) (symmetry.mapState t)
  | _, _, .nil _ => .nil _
  | s, _, .cons (u := u) action step tail => by
      have mappedStep :
          tryMove (symmetry.mapState s) (symmetry.mapAction action).piece
            (symmetry.mapAction action).direction = some (symmetry.mapState u) := by
        rw [symmetry.move_commutes, step]
        rfl
      exact .cons (symmetry.mapAction action) mappedStep (symmetry.mapPath tail)

noncomputable def mapSolution (symmetry : GameSymmetry)
    (solution : Solution start) : Solution (symmetry.mapState start) where
  target := symmetry.mapState solution.target
  path := symmetry.mapPath solution.path
  solved := by rw [symmetry.goal_invariant]; exact solution.solved

theorem solution_iff (symmetry : GameSymmetry) :
    Nonempty (Solution start) ↔ Nonempty (Solution (symmetry.mapState start)) := by
  constructor
  · rintro ⟨solution⟩
    exact ⟨symmetry.mapSolution solution⟩
  · rintro ⟨solution⟩
    have mapped := symmetry.mapSolution solution
    rw [symmetry.involutiveState] at mapped
    exact ⟨mapped⟩

end GameSymmetry

end Huarongdao
