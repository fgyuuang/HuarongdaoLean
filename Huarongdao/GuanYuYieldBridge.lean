import Huarongdao.GuanYuYield

namespace Huarongdao
namespace QPath

/-- Action-sensitive event tracking for quotient paths.  The transition is
evaluated on the exact representative source and exact executable successor
stored by the constructor. -/
def UsesTransition :
    {source target : State} → QPath source target →
      (State → Action → State → Prop) → Prop
  | _, _, .nil _, _ => False
  | source, _, .cons (actual := actual) action _executed _represented tail,
      selected =>
      selected source action actual ∨ UsesTransition tail selected

theorem UsesTransition_ofPath_iff
    {source target : State} (path : Path source target) :
    (QPath.ofPath path).UsesTransition GuanYuYield ↔
      path.UsesTransition GuanYuYield := by
  induction path with
  | nil =>
      rfl
  | cons action executed tail inductionHypothesis =>
      simp [QPath.ofPath, UsesTransition, Path.UsesTransition,
        inductionHypothesis]

end QPath

namespace GuanYuYieldTheory

open CaoGuanGeometry

/-- Lift one concrete non-yield move from a state to an arbitrary equal-shape
representative of that state.  The target representative is the relabelled
concrete target, and the transported action remains non-yielding. -/
theorem liftNoYieldStep
    {source representative target : State}
    (sourceValid : ValidState source)
    (representativeValid : ValidState representative)
    (targetValid : ValidState target)
    (same : SameShape source representative)
    {action : Action}
    (executed : tryMove source action.piece action.direction = some target)
    (notYield : ¬ GuanYuYield source action target) :
    ∃ representativeAction representativeTarget,
      tryMove representative representativeAction.piece
          representativeAction.direction = some representativeTarget ∧
      ¬ GuanYuYield representative representativeAction representativeTarget ∧
      SameShape target representativeTarget := by
  let relabeling :=
    sameShapeRelabeling sourceValid representativeValid same
  have sourceEq :
      relabelState relabeling source = representative :=
    sameShapeRelabeling_eq sourceValid representativeValid same
  let representativeAction := relabelAction relabeling action
  let representativeTarget := relabelState relabeling target
  have transported :
      tryMove (relabelState relabeling source)
          representativeAction.piece representativeAction.direction =
        some representativeTarget := by
    exact tryMove_relabel_some relabeling executed
  have representativeStep :
      tryMove representative
          representativeAction.piece representativeAction.direction =
        some representativeTarget := by
    rw [← sourceEq]
    exact transported
  have representativeNotYield :
      ¬ GuanYuYield representative representativeAction representativeTarget := by
    intro contradiction
    apply notYield
    have restored :=
      (GuanYuYield.relabel_iff relabeling sourceValid targetValid).mpr
        (by
          simpa [representativeAction, representativeTarget, ← sourceEq] using
            contradiction)
    exact restored
  refine ⟨representativeAction, representativeTarget,
    representativeStep, representativeNotYield, ?_⟩
  exact sameShape_symm (relabel_sameShape relabeling target)

/-- A concrete non-yield path can be lifted step by step to a quotient path
whose constructors retain exact executable representatives. -/
theorem liftNoYieldPath
    {source target representative : State}
    (sourceValid : ValidState source)
    (representativeValid : ValidState representative)
    (same : SameShape source representative)
    (path : Path source target)
    (notYield : ¬ path.UsesTransition GuanYuYield) :
    ∃ representativeTarget, ∃ representativePath : QPath representative representativeTarget,
      SameShape target representativeTarget ∧
      ¬ representativePath.UsesTransition GuanYuYield := by
  induction path generalizing representative with
  | nil =>
      refine ⟨representative, .nil representative, ?_, ?_⟩
      · exact same
      · simp [QPath.UsesTransition]
  | @cons source middle target action executed tail inductionHypothesis =>
      have middleValid : ValidState middle :=
        tryMove_preserves_validity executed
      have firstNotYield : ¬ GuanYuYield source action middle := by
        intro yield
        exact notYield (Or.inl yield)
      obtain ⟨representativeAction, middleRepresentative,
          representativeStep, representativeNotYield, targetShape⟩ :=
        liftNoYieldStep sourceValid representativeValid middleValid
          same executed firstNotYield
      have tailNotYield : ¬ tail.UsesTransition GuanYuYield := by
        intro later
        exact notYield (Or.inr later)
      have middleRepresentativeValid : ValidState middleRepresentative :=
        tryMove_preserves_validity representativeStep
      obtain ⟨representativeTarget, representativeTail,
          finalShape, tailNoYield⟩ :=
        inductionHypothesis (representative := middleRepresentative)
          middleValid
          middleRepresentativeValid
          targetShape tailNotYield
      refine ⟨representativeTarget,
        .cons representativeAction representativeStep
          (sameShape_refl middleRepresentative) representativeTail,
        ?_, ?_⟩
      · exact finalShape
      · intro uses
        change GuanYuYield representative representativeAction middleRepresentative ∨
          representativeTail.UsesTransition GuanYuYield at uses
        rcases uses with first | later
        · exact representativeNotYield first
        · exact tailNoYield later

theorem liftNoYieldSolution
    (solution : Solution classic)
    (notYield : ¬ solution.path.UsesTransition GuanYuYield) :
    ∃ representativeTarget, ∃ representativePath : QPath classic representativeTarget,
      SameShape solution.target representativeTarget ∧
      ¬ representativePath.UsesTransition GuanYuYield := by
  exact liftNoYieldPath classic_valid classic_valid
    (sameShape_refl classic) solution.path notYield

/-- The lifted endpoint is still a goal state.  This is the endpoint half of
the contradiction used when a finite quotient search excludes all goals. -/
theorem liftNoYieldSolution_goal
    (solution : Solution classic)
    (notYield : ¬ solution.path.UsesTransition GuanYuYield) :
    ∃ representativeTarget, ∃ representativePath : QPath classic representativeTarget,
      SameShape solution.target representativeTarget ∧
      goal representativeTarget = true ∧
      ¬ representativePath.UsesTransition GuanYuYield := by
  rcases liftNoYieldSolution solution notYield with
    ⟨representativeTarget, representativePath, sameTarget, noYield⟩
  refine ⟨representativeTarget, representativePath, sameTarget, ?_, noYield⟩
  calc
    goal representativeTarget = goal solution.target := (sameShape_goal sameTarget).symm
    _ = true := solution.solved

end GuanYuYieldTheory
end Huarongdao
