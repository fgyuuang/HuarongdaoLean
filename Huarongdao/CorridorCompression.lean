import Huarongdao.MirrorQuotient

open Huarongdao

namespace Huarongdao

/-!
This module is a derived state space over `MirrorShapeState`. It does not
identify additional states. Instead, it packages maximal non-branching walks
as weighted macro transitions whose full mirror-quotient walk is retained.
-/

/-- The initial node of the maintained horizontal-mirror quotient. -/
def mirrorShapeInitial : MirrorShapeState :=
  MirrorShapeState.ofShapeState shapeGraphTask.initial

/--
A node is an interior corridor node when it has exactly two distinct outgoing
neighbours after edge labels have been forgotten.
-/
def CorridorInterior (node : MirrorShapeState) : Prop :=
  ∃ left right,
    left ≠ right ∧
    MirrorShapeStep node left ∧
    MirrorShapeStep node right ∧
    ∀ target, MirrorShapeStep node target → target = left ∨ target = right

/--
Initial, goal, and branching/dead-end nodes are retained as corridor anchors.
Only non-goal degree-two nodes may disappear from the rendered macro graph.
-/
def CorridorAnchor (node : MirrorShapeState) : Prop :=
  node = mirrorShapeInitial ∨
  MirrorShapeGoal node ∨
  ¬ CorridorInterior node

/-- Nodes of the corridor-compressed graph. -/
abbrev CorridorState := { node : MirrorShapeState // CorridorAnchor node }

/--
After entering `current` from `previous`, `next` is the only legal forward
choice other than immediately returning to `previous`.
-/
structure UniqueForward
    (previous current next : MirrorShapeState) : Prop where
  distinct : next ≠ previous
  step : MirrorShapeStep current next
  unique :
    ∀ candidate,
      MirrorShapeStep current candidate →
      candidate ≠ previous →
      candidate = next

/--
The proof-carrying remainder of one forced corridor. `next` may only pass
through nodes that are not anchors, so an anchor always terminates the macro.
-/
inductive ForcedTail :
    MirrorShapeState → MirrorShapeState → MirrorShapeState → Type where
  | stop (previous current : MirrorShapeState) :
      ForcedTail previous current current
  | next {previous current next target : MirrorShapeState}
      (current_not_anchor : ¬ CorridorAnchor current)
      (forced : UniqueForward previous current next)
      (tail : ForcedTail current next target) :
      ForcedTail previous current target

/-- A proof-carrying walk in the mirror quotient. -/
abbrev MirrorShapeWalk (source target : MirrorShapeState) :=
  mirrorShapeTask.Walk source target

/-- Concatenate two walks in the mirror quotient. -/
def appendMirrorShapeWalk
    (left : MirrorShapeWalk source middle)
    (right : MirrorShapeWalk middle target) :
    MirrorShapeWalk source target :=
  left.append right

@[simp] theorem appendMirrorShapeWalk_length
    (left : MirrorShapeWalk source middle)
    (right : MirrorShapeWalk middle target) :
    (appendMirrorShapeWalk left right).length =
      left.length + right.length := by
  exact left.length_append right

namespace ForcedTail

/-- Expand a forced tail back to its complete mirror-quotient walk. -/
def toWalk :
    {previous current target : MirrorShapeState} →
      ForcedTail previous current target →
      MirrorShapeWalk current target
  | _, _, _, .stop _ _ => .nil _
  | _, _, _, .next _ forced tail =>
      .cons () forced.step (toWalk tail)

end ForcedTail

/--
One macro transition between retained corridor anchors. The first edge and
every suppressed intermediate edge remain available as a formal walk.
-/
structure CorridorMacroStep (source target : CorridorState) where
  firstNode : MirrorShapeState
  first : MirrorShapeStep source.1 firstNode
  tail : ForcedTail source.1 firstNode target.1

namespace CorridorMacroStep

/-- Expand a macro transition into the underlying mirror-quotient walk. -/
def toWalk (segment : CorridorMacroStep source target) :
    MirrorShapeWalk source.1 target.1 :=
  .cons () segment.first segment.tail.toWalk

/-- Number of primitive mirror-quotient transitions represented by the macro. -/
def weight (segment : CorridorMacroStep source target) : Nat :=
  segment.toWalk.length

theorem weight_positive (segment : CorridorMacroStep source target) :
    0 < segment.weight := by
  simp [weight, toWalk, StateSpace.Task.Walk.length]

/-- A direct edge between anchors is a corridor macro of weight one. -/
def ofStep (step : MirrorShapeStep source.1 target.1) :
    CorridorMacroStep source target where
  firstNode := target.1
  first := step
  tail := .stop source.1 target.1

@[simp] theorem weight_ofStep
    {source target : CorridorState}
    (step : MirrorShapeStep source.1 target.1) :
    (ofStep step).weight = 1 := by
  rfl

end CorridorMacroStep

/--
The independent corridor-compressed task. Its actions are primitive-step
weights, while its transition relation requires a proof-carrying macro.
-/
def corridorTask : StateSpace.Task CorridorState Nat where
  initial := ⟨mirrorShapeInitial, Or.inl rfl⟩
  goal := fun state => MirrorShapeGoal state.1
  step := fun source weight target =>
    ∃ segment : CorridorMacroStep source target, segment.weight = weight

/-- A retained direct mirror edge transfers upward as a weight-one macro edge. -/
theorem corridorStep_of_mirrorStep
    {source target : CorridorState}
    (step : MirrorShapeStep source.1 target.1) :
    corridorTask.step source 1 target := by
  change ∃ segment : CorridorMacroStep source target, segment.weight = 1
  exact ⟨CorridorMacroStep.ofStep step,
    CorridorMacroStep.weight_ofStep step⟩

/-- Extract the proof-carrying macro represented by one corridor-task edge. -/
noncomputable def corridorStepSegment
    {source target : CorridorState} {weight : Nat}
    (step : corridorTask.step source weight target) :
    CorridorMacroStep source target := by
  change ∃ segment : CorridorMacroStep source target,
    segment.weight = weight at step
  exact step.choose

theorem corridorStepSegment_weight
    {source target : CorridorState} {weight : Nat}
    (step : corridorTask.step source weight target) :
    (corridorStepSegment step).weight = weight := by
  change ∃ segment : CorridorMacroStep source target,
    segment.weight = weight at step
  exact step.choose_spec

/-- Every macro-task edge expands to a mirror-quotient walk of its weight. -/
theorem corridorStep_expand
    {source target : CorridorState} {weight : Nat}
    (step : corridorTask.step source weight target) :
    ∃ walk : MirrorShapeWalk source.1 target.1,
      walk.length = weight := by
  change ∃ segment : CorridorMacroStep source target,
    segment.weight = weight at step
  rcases step with ⟨segment, rfl⟩
  exact ⟨segment.toWalk, rfl⟩

/-- Expand a whole corridor-task walk into the underlying mirror quotient. -/
noncomputable def corridorWalkExpand :
    {source target : CorridorState} →
      corridorTask.Walk source target →
      MirrorShapeWalk source.1 target.1
  | _, _, .nil _ => .nil _
  | _, _, .cons _weight first tail =>
      appendMirrorShapeWalk
        (corridorStepSegment first).toWalk
        (corridorWalkExpand tail)

/--
Expansion preserves primitive cost: summing macro weights gives exactly the
number of underlying mirror-quotient transitions.
-/
theorem corridorWalkExpand_length
    (walk : corridorTask.Walk source target) :
    (corridorWalkExpand walk).length = walk.actions.sum := by
  induction walk with
  | nil => rfl
  | @cons source middle target weight first tail ih =>
      have chosenWeight :
          (corridorStepSegment first).weight = weight :=
        corridorStepSegment_weight first
      have chosenWalkLength :
          (corridorStepSegment first).toWalk.length = weight := by
        simpa [CorridorMacroStep.weight] using chosenWeight
      rw [corridorWalkExpand, appendMirrorShapeWalk_length,
        chosenWalkLength, ih]
      rfl

/--
Every corridor walk lifts through the mirror quotient to an equal-cost walk
in the preceding equal-shape state space.
-/
theorem corridorWalk_liftToShapeWithCost
    (walk : corridorTask.Walk source target)
    (sourceRepresentative : ShapeState)
    (source_eq :
      MirrorShapeState.ofShapeState sourceRepresentative = source.1) :
    ∃ targetRepresentative,
      ∃ shapeWalk : shapeGraphTask.Walk
          sourceRepresentative targetRepresentative,
        shapeWalk.length = walk.actions.sum ∧
        MirrorShapeState.ofShapeState targetRepresentative = target.1 := by
  rcases mirrorShapeTask_liftWalkWithLength
      (corridorWalkExpand walk) sourceRepresentative source_eq with
    ⟨targetRepresentative, shapeWalk, length_eq, target_eq⟩
  exact ⟨targetRepresentative, shapeWalk,
    length_eq.trans (corridorWalkExpand_length walk), target_eq⟩

/--
Every corridor-compressed walk expands through both quotient layers to an
equal-cost walk in the concrete valid-state task.
-/
theorem corridorWalk_liftToConcreteWithCost
    (walk : corridorTask.Walk source target)
    (sourceRepresentative : ValidClassicState)
    (source_eq :
      MirrorShapeState.ofState sourceRepresentative = source.1) :
    ∃ targetRepresentative,
      ∃ concreteWalk : validClassicTask.Walk
          sourceRepresentative targetRepresentative,
        concreteWalk.length = walk.actions.sum ∧
        MirrorShapeState.ofState targetRepresentative = target.1 := by
  rcases mirrorShapeTask_liftToConcreteWithLength
      (corridorWalkExpand walk) sourceRepresentative source_eq with
    ⟨targetRepresentative, concreteWalk, length_eq, target_eq⟩
  exact ⟨targetRepresentative, concreteWalk,
    length_eq.trans (corridorWalkExpand_length walk), target_eq⟩

/-- The derived task inherits the mirror-quotient goal predicate unchanged. -/
theorem corridorGoal_iff (state : CorridorState) :
    corridorTask.goal state ↔ MirrorShapeGoal state.1 :=
  by
    change MirrorShapeGoal state.1 ↔ MirrorShapeGoal state.1
    exact Iff.rfl

end Huarongdao
