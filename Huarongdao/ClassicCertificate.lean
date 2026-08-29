import Huarongdao.ClassicSolution
import Huarongdao.Search
import Huarongdao.StateSpaceKernel
import Std.Tactic

namespace Huarongdao

/-- The complete equal-shape finite presentation rooted at the classic layout. -/
def classicQuotientGraph : Graph :=
  enumerate classic

 /-- Certificate that every representative in the classic quotient array is a
    valid puzzle state. -/
structure ClassicQuotientGraphCertificate (graph : Graph) where
  valid : ∀ vertex : Fin graph.states.size, ValidState graph.states[vertex]

/-- Native evaluation checks the certificate conditions for the complete
    classic quotient graph. -/
def classicQuotientGraphCertificate : ClassicQuotientGraphCertificate classicQuotientGraph where
  valid := by
    set_option maxHeartbeats 0 in
    intro vertex
    native_decide

/-- Native evaluation checks the complete finite graph conditions consumed by
    the generic soundness theorem in `Search.lean`. -/
theorem classicQuotientLowerBound_checked :
    checkQuotientLowerBound classicQuotientGraph classic 116 = true := by
  set_option maxHeartbeats 0 in
  native_decide

/-- A proof-carrying lower-bound certificate for the complete classic graph. -/
noncomputable def classicQuotientLowerBoundCertificate :
    QuotientLowerBoundCertificate classic 116 :=
  Classical.choice
    (checkQuotientLowerBound_sound
      classicQuotientLowerBound_checked)

/-- The checked 116-move play is globally minimal among executable plays. -/
theorem classic116Play_minimal :
    classic116Play.Minimal := by
  intro other
  rw [classic116Play_length]
  exact
    classicQuotientLowerBoundCertificate.play_lower_bound other

private theorem pathOfClassicWalk_length
    (walk : StateSpace.classicTask.Walk source target) :
    (StateSpace.pathOfClassicWalk walk).length = walk.length := by
  induction walk with
  | nil =>
      rfl
  | cons action first tail inductionHypothesis =>
      simp [
        StateSpace.pathOfClassicWalk,
        Path.length,
        StateSpace.Task.Walk.length,
        inductionHypothesis
      ]

/-- The finite certificate supplies the same lower bound directly to the raw
    `StateSpace.Task` representation of the classic puzzle. -/
theorem classicTask_solution_lower_bound
    (solution : StateSpace.classicTask.Solution) :
    116 ≤ solution.walk.length := by
  let concreteSolution : Solution classic := {
    target := solution.target
    path := StateSpace.pathOfClassicWalk solution.walk
    solved := solution.solved
  }
  have lower :=
    classicQuotientLowerBoundCertificate.solution_lower_bound
      concreteSolution
  change 116 ≤
    (StateSpace.pathOfClassicWalk solution.walk).length at lower
  rw [pathOfClassicWalk_length] at lower
  exact lower

namespace ClassicStateSpaceKernel

/-- Forget the validity proof while preserving every concrete action and step. -/
def concreteToRaw :
    StateSpace.Task.Hom concrete StateSpace.classicTask where
  mapState := fun state => state.1
  mapAction := id
  map_initial := rfl
  map_goal := fun solved => solved
  map_step := fun executed => executed

/-- Every solution of the maintained concrete state-space task has length at
    least 116 primitive moves. -/
theorem concreteSolution_lower_bound
    (solution : concrete.Solution) :
    116 ≤ solution.walk.length := by
  let rawSolution : StateSpace.classicTask.Solution := {
    target := solution.target.1
    walk := concreteToRaw.mapWalk solution.walk
    solved := solution.solved
  }
  have lower := classicTask_solution_lower_bound rawSolution
  change 116 ≤ (concreteToRaw.mapWalk solution.walk).length at lower
  rw [concreteToRaw.mapWalk_length] at lower
  exact lower

end ClassicStateSpaceKernel

end Huarongdao
