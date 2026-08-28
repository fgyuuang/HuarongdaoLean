import Huarongdao.ClassicCertificate

namespace Huarongdao
namespace StateSpace

universe u v

namespace Task

variable {State : Type u} {Action : Type v}

/-- There is a proof-carrying walk of exactly `distance` primitive steps. -/
def HasWalkLength (task : Task State Action)
    (source target : State) (distance : Nat) : Prop :=
  ∃ walk : task.Walk source target, walk.length = distance

/-- The task has a goal-reaching solution of exactly `distance` primitive steps. -/
def HasSolutionLength (task : Task State Action) (distance : Nat) : Prop :=
  ∃ solution : task.Solution, solution.length = distance

/-- `distance` is the least length of any goal-reaching solution. -/
def ShortestSolutionLength (task : Task State Action) (distance : Nat) : Prop :=
  task.HasSolutionLength distance ∧
    ∀ candidate, task.HasSolutionLength candidate → distance ≤ candidate

theorem shortestSolutionLength_unique
    {task : Task State Action} {left right : Nat}
    (leftShortest : task.ShortestSolutionLength left)
    (rightShortest : task.ShortestSolutionLength right) :
    left = right :=
  Nat.le_antisymm
    (leftShortest.2 right rightShortest.1)
    (rightShortest.2 left leftShortest.1)

end Task

namespace BisimulationQuotient

variable {State : Type u} {Action : Type v}
variable {task : Task State Action}

/--
An exact-length quotient walk is equivalent to an exact-length concrete walk
ending in some representative of the target class.
-/
theorem hasWalkLength_quotient_iff
    (quotient : BisimulationQuotient task)
    (source : State)
    (targetClass : quotient.toObservation.Node)
    (distance : Nat) :
    quotient.toObservation.quotientTask.HasWalkLength
        (quotient.toObservation.classOf source) targetClass distance ↔
      ∃ target : State,
        task.HasWalkLength source target distance ∧
        quotient.toObservation.classOf target = targetClass := by
  constructor
  · rintro ⟨quotientWalk, quotientLength⟩
    rcases quotient.liftTaskWalkWithLength quotientWalk source rfl with
      ⟨target, concreteWalk, concreteLength, targetClassEq⟩
    exact
      ⟨target, ⟨concreteWalk, concreteLength.trans quotientLength⟩,
        targetClassEq⟩
  · rintro ⟨target, ⟨concreteWalk, concreteLength⟩, targetClassEq⟩
    rw [← targetClassEq]
    refine
      ⟨quotient.toObservation.projectionHom.mapWalk concreteWalk, ?_⟩
    exact
      (quotient.toObservation.projectionHom.mapWalk_length concreteWalk).trans
        concreteLength

/--
Exact solution lengths are invariant under a bisimulation quotient. This is
the main replacement for running shortest-path arguments on labelled states.
-/
theorem hasSolutionLength_iff_quotient
    (quotient : BisimulationQuotient task)
    (distance : Nat) :
    task.HasSolutionLength distance ↔
      quotient.toObservation.quotientTask.HasSolutionLength distance := by
  constructor
  · rintro ⟨solution, solutionLength⟩
    let quotientWalk :=
      quotient.toObservation.projectionHom.mapWalk solution.walk
    let quotientSolution :
        quotient.toObservation.quotientTask.Solution := {
      target := quotient.toObservation.classOf solution.target
      walk := quotientWalk
      solved := quotient.toObservation.projectionHom.map_goal solution.solved
    }
    refine ⟨quotientSolution, ?_⟩
    change quotientWalk.length = distance
    exact
      (quotient.toObservation.projectionHom.mapWalk_length solution.walk).trans
        solutionLength
  · rintro ⟨solution, solutionLength⟩
    rcases quotient.liftTaskWalkWithLength
        solution.walk task.initial rfl with
      ⟨target, concreteWalk, concreteLength, targetClassEq⟩
    have targetGoal : task.goal target := by
      apply (quotient.toObservation.goal_classOf target).mp
      rw [targetClassEq]
      exact solution.solved
    let concreteSolution : task.Solution := {
      target := target
      walk := concreteWalk
      solved := targetGoal
    }
    refine ⟨concreteSolution, ?_⟩
    change concreteWalk.length = distance
    change solution.walk.length = distance at solutionLength
    exact concreteLength.trans solutionLength

/-- A bisimulation quotient preserves the least goal-reaching path length. -/
theorem shortestSolutionLength_iff_quotient
    (quotient : BisimulationQuotient task)
    (distance : Nat) :
    task.ShortestSolutionLength distance ↔
      quotient.toObservation.quotientTask.ShortestSolutionLength distance := by
  constructor
  · intro concreteShortest
    constructor
    · exact
        (quotient.hasSolutionLength_iff_quotient distance).mp
          concreteShortest.1
    · intro candidate quotientCandidate
      apply concreteShortest.2 candidate
      exact
        (quotient.hasSolutionLength_iff_quotient candidate).mpr
          quotientCandidate
  · intro quotientShortest
    constructor
    · exact
        (quotient.hasSolutionLength_iff_quotient distance).mpr
          quotientShortest.1
    · intro candidate concreteCandidate
      apply quotientShortest.2 candidate
      exact
        (quotient.hasSolutionLength_iff_quotient candidate).mp
          concreteCandidate

end BisimulationQuotient
end StateSpace

namespace ClassicStateSpaceKernel

/-- Convert a labelled classic path into the legal-state task. -/
noncomputable def pathToConcreteWalk
    (path : Path source target)
    (sourceValid : ValidState source) :
      concrete.Walk
        ⟨source, sourceValid⟩
        ⟨target, path.target_valid sourceValid⟩ := by
  induction path with
  | nil =>
      exact .nil _
  | @cons source middle target action executed tail inductionHypothesis =>
      let middleValid : ValidState middle :=
        tryMove_preserves_validity executed
      have first :
          concrete.step
            ⟨source, sourceValid⟩ action
            ⟨middle, middleValid⟩ :=
        executed
      exact
        .cons action first
          (inductionHypothesis middleValid)

@[simp] theorem pathToConcreteWalk_length
    (path : Path source target)
    (sourceValid : ValidState source) :
    (pathToConcreteWalk path sourceValid).length = path.length := by
  induction path with
  | nil =>
      rfl
  | cons action executed tail inductionHypothesis =>
      change
        (pathToConcreteWalk tail
          (tryMove_preserves_validity executed)).length + 1 =
          tail.length + 1
      rw [inductionHypothesis]

/--
A successful action execution determines a concrete legal-state walk of the
same primitive length. The validity witness is returned with the walk.
-/
theorem existsConcreteWalkOfRunMoves
    {source target : State} {actions : List Action}
    (sourceValid : ValidState source)
    (executed : runMoves source actions = some target) :
    ∃ targetValid : ValidState target,
      ∃ walk : concrete.Walk
          ⟨source, sourceValid⟩
          ⟨target, targetValid⟩,
        walk.length = actions.length := by
  induction actions generalizing source with
  | nil =>
      simp [runMoves] at executed
      subst target
      exact ⟨sourceValid, .nil _, rfl⟩
  | cons action rest inductionHypothesis =>
      cases moved :
          tryMove source action.piece action.direction with
      | none =>
          simp [runMoves, moved] at executed
      | some next =>
          have tailExecuted :
              runMoves next rest = some target := by
            simpa [runMoves, moved] using executed
          let nextValid : ValidState next :=
            tryMove_preserves_validity moved
          rcases inductionHypothesis nextValid tailExecuted with
            ⟨targetValid, tailWalk, tailLength⟩
          have first :
              concrete.step
                ⟨source, sourceValid⟩ action
                ⟨next, nextValid⟩ :=
            moved
          refine
            ⟨targetValid, .cons action first tailWalk, ?_⟩
          simp [StateSpace.Task.Walk.length, tailLength]

/-- The maintained 116-step witness as a solution of the legal concrete task. -/
theorem concrete_hasSolutionLength_116 :
    concrete.HasSolutionLength 116 := by
  rcases existsConcreteWalkOfRunMoves
      classic_valid classic116_runs with
    ⟨targetValid, walk, walkLength⟩
  let solution : concrete.Solution := {
    target := ⟨classic116Goal, targetValid⟩
    walk := walk
    solved := classic116_reaches_goal
  }
  refine ⟨solution, ?_⟩
  change walk.length = 116
  exact walkLength.trans classic116_length

/-- The concrete legal-state task has a globally shortest solution of length 116. -/
theorem concrete_shortestSolutionLength_116 :
    concrete.ShortestSolutionLength 116 := by
  constructor
  · exact concrete_hasSolutionLength_116
  · rintro candidate ⟨solution, solutionLength⟩
    have lower := concreteSolution_lower_bound solution
    change solution.walk.length = candidate at solutionLength
    exact solutionLength ▸ lower

/-- Equal-shape quotienting preserves every possible solution length. -/
theorem concrete_hasSolutionLength_iff_shape (distance : Nat) :
    concrete.HasSolutionLength distance ↔
      shape.HasSolutionLength distance :=
  concreteShapeQuotient.hasSolutionLength_iff_quotient distance

/-- Horizontal reflection quotienting preserves every possible solution length. -/
theorem shape_hasSolutionLength_iff_mirror (distance : Nat) :
    shape.HasSolutionLength distance ↔
      mirror.HasSolutionLength distance :=
  shapeMirrorQuotient.hasSolutionLength_iff_quotient distance

/-- The full two-stage symmetry quotient preserves every solution length. -/
theorem concrete_hasSolutionLength_iff_mirror (distance : Nat) :
    concrete.HasSolutionLength distance ↔
      mirror.HasSolutionLength distance :=
  (concrete_hasSolutionLength_iff_shape distance).trans
    (shape_hasSolutionLength_iff_mirror distance)

/-- Equal-shape quotienting preserves the exact shortest solution length. -/
theorem concrete_shortestSolutionLength_iff_shape (distance : Nat) :
    concrete.ShortestSolutionLength distance ↔
      shape.ShortestSolutionLength distance :=
  concreteShapeQuotient.shortestSolutionLength_iff_quotient distance

/-- Horizontal reflection quotienting preserves the exact shortest solution length. -/
theorem shape_shortestSolutionLength_iff_mirror (distance : Nat) :
    shape.ShortestSolutionLength distance ↔
      mirror.ShortestSolutionLength distance :=
  shapeMirrorQuotient.shortestSolutionLength_iff_quotient distance

/-- The mirror quotient is a complete basis for primitive-step shortest paths. -/
theorem concrete_shortestSolutionLength_iff_mirror (distance : Nat) :
    concrete.ShortestSolutionLength distance ↔
      mirror.ShortestSolutionLength distance :=
  (concrete_shortestSolutionLength_iff_shape distance).trans
    (shape_shortestSolutionLength_iff_mirror distance)

/-- The classic mirror quotient has shortest goal distance exactly 116. -/
theorem mirror_shortestSolutionLength_116 :
    mirror.ShortestSolutionLength 116 :=
  (concrete_shortestSolutionLength_iff_mirror 116).mp
    concrete_shortestSolutionLength_116

/-- The intermediate equal-shape quotient has shortest goal distance exactly 116. -/
theorem shape_shortestSolutionLength_116 :
    shape.ShortestSolutionLength 116 :=
  (concrete_shortestSolutionLength_iff_shape 116).mp
    concrete_shortestSolutionLength_116

end ClassicStateSpaceKernel
end Huarongdao
