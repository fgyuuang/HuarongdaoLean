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
At a suppressed degree-two node, a reversible incoming edge and a distinct
outgoing edge determine the outgoing edge uniquely.
-/
theorem uniqueForward_of_not_anchor
    {previous current next : MirrorShapeState}
    (current_not_anchor : ¬ CorridorAnchor current)
    (reverse : MirrorShapeStep current previous)
    (forward : MirrorShapeStep current next)
    (distinct : next ≠ previous) :
    UniqueForward previous current next := by
  have interior : CorridorInterior current :=
    Classical.byContradiction fun notInterior =>
      current_not_anchor (Or.inr (Or.inr notInterior))
  rcases interior with
    ⟨left, right, _left_ne_right, _leftStep, _rightStep, complete⟩
  refine ⟨distinct, forward, ?_⟩
  intro candidate candidateStep candidate_ne_previous
  have previous_cases := complete previous reverse
  have next_cases := complete next forward
  have candidate_cases := complete candidate candidateStep
  rcases previous_cases with previous_eq_left | previous_eq_right
  · have next_eq_right : next = right := by
      rcases next_cases with next_eq_left | next_eq_right
      · exact (distinct (next_eq_left.trans previous_eq_left.symm)).elim
      · exact next_eq_right
    have candidate_eq_right : candidate = right := by
      rcases candidate_cases with candidate_eq_left | candidate_eq_right
      · exact
          (candidate_ne_previous
            (candidate_eq_left.trans previous_eq_left.symm)).elim
      · exact candidate_eq_right
    exact candidate_eq_right.trans next_eq_right.symm
  · have next_eq_left : next = left := by
      rcases next_cases with next_eq_left | next_eq_right
      · exact next_eq_left
      · exact (distinct (next_eq_right.trans previous_eq_right.symm)).elim
    have candidate_eq_left : candidate = left := by
      rcases candidate_cases with candidate_eq_left | candidate_eq_right
      · exact candidate_eq_left
      · exact
          (candidate_ne_previous
            (candidate_eq_right.trans previous_eq_right.symm)).elim
    exact candidate_eq_left.trans next_eq_left.symm

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
Evidence that a concrete mirror-quotient walk is the reduced remainder of one
corridor segment. Every suppressed current node is non-anchor, the edge used
to enter it is reversible, and the next node is not an immediate return to the
previous node.

Reversibility is stated locally instead of being assumed globally for
`MirrorShapeStep`. This is exactly the hypothesis needed to turn degree two
into a unique forward choice.
-/
inductive ReducedCorridorTail :
    (previous : MirrorShapeState) →
      {current target : MirrorShapeState} →
      MirrorShapeWalk current target → Type where
  | stop (current : MirrorShapeState) :
      ReducedCorridorTail previous (.nil current)
  | next {current next target : MirrorShapeState}
      {tail : MirrorShapeWalk next target}
      (current_not_anchor : ¬ CorridorAnchor current)
      (reverse : MirrorShapeStep current previous)
      (forward : MirrorShapeStep current next)
      (distinct : next ≠ previous)
      (rest : ReducedCorridorTail current tail) :
      ReducedCorridorTail previous (.cons () forward tail)

namespace ReducedCorridorTail

/-- Convert the local reduced-walk evidence into the existing forced-tail form. -/
def toForcedTail :
    {previous current target : MirrorShapeState} →
    {walk : MirrorShapeWalk current target} →
      ReducedCorridorTail previous walk →
      ForcedTail previous current target
  | _, _, _, _, .stop _ => .stop _ _
  | _, _, _, _, .next current_not_anchor reverse forward distinct rest =>
      .next current_not_anchor
        (uniqueForward_of_not_anchor
          current_not_anchor reverse forward distinct)
        (toForcedTail rest)

/-- Conversion retains the exact mirror-quotient walk, not only its length. -/
@[simp] theorem toForcedTail_toWalk
    {walk : MirrorShapeWalk current target}
    (reduced : ReducedCorridorTail previous walk) :
    reduced.toForcedTail.toWalk = walk := by
  induction reduced with
  | stop => rfl
  | next current_not_anchor reverse forward distinct rest ih =>
      simp [toForcedTail, ForcedTail.toWalk, ih]

end ReducedCorridorTail

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
A reduced concrete segment between two retained anchors. The first edge is
stored separately because the reduced-tail condition only applies after the
walk has entered a possible corridor interior.
-/
structure ReducedCorridorSegment (source target : CorridorState) where
  firstNode : MirrorShapeState
  first : MirrorShapeStep source.1 firstNode
  tailWalk : MirrorShapeWalk firstNode target.1
  reduced : ReducedCorridorTail source.1 tailWalk

namespace ReducedCorridorSegment

/-- The original mirror-quotient walk represented by a reduced segment. -/
def toWalk (segment : ReducedCorridorSegment source target) :
    MirrorShapeWalk source.1 target.1 :=
  .cons () segment.first segment.tailWalk

/-- Every reduced reversible segment determines a forced corridor macro. -/
def toMacroStep (segment : ReducedCorridorSegment source target) :
    CorridorMacroStep source target where
  firstNode := segment.firstNode
  first := segment.first
  tail := segment.reduced.toForcedTail

/-- Segment conversion preserves the complete underlying walk. -/
@[simp] theorem toMacroStep_toWalk
    (segment : ReducedCorridorSegment source target) :
    segment.toMacroStep.toWalk = segment.toWalk := by
  simp [toMacroStep, CorridorMacroStep.toWalk, toWalk]

/-- Segment conversion preserves primitive transition count. -/
@[simp] theorem toMacroStep_weight
    (segment : ReducedCorridorSegment source target) :
    segment.toMacroStep.weight = segment.toWalk.length := by
  simp [CorridorMacroStep.weight]

end ReducedCorridorSegment

/--
A segmentation of a mirror-quotient walk at retained anchors. Each constituent
segment satisfies exactly the local reversibility and no-immediate-backtrack
hypotheses required by `ReducedCorridorSegment`.
-/
inductive CorridorSegmentation : CorridorState → CorridorState → Type where
  | nil (state : CorridorState) :
      CorridorSegmentation state state
  | cons {source middle target : CorridorState}
      (first : ReducedCorridorSegment source middle)
      (rest : CorridorSegmentation middle target) :
      CorridorSegmentation source target

namespace CorridorSegmentation

/-- Reassemble all concrete segments into one mirror-quotient walk. -/
def toMirrorWalk :
    {source target : CorridorState} →
      CorridorSegmentation source target →
      MirrorShapeWalk source.1 target.1
  | _, _, .nil state => .nil state.1
  | _, _, .cons first rest =>
      appendMirrorShapeWalk first.toWalk (toMirrorWalk rest)

end CorridorSegmentation

/--
Evidence that a given mirror-quotient walk admits the exact reduced anchor
segmentation required by corridor compression.
-/
structure CorridorSegmentationOf
    {source target : CorridorState}
    (walk : MirrorShapeWalk source.1 target.1) where
  segmentation : CorridorSegmentation source target
  realizes : segmentation.toMirrorWalk = walk

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

/-- Primitive cost of a corridor walk, obtained by summing its macro weights. -/
def corridorWalkCost
    (walk : corridorTask.Walk source target) : Nat :=
  walk.actions.sum

namespace CorridorSegmentation

/--
Compress an explicitly segmented reduced mirror walk into the weighted
corridor task.
-/
def toCorridorWalk :
    {source target : CorridorState} →
      CorridorSegmentation source target →
      corridorTask.Walk source target
  | _, _, .nil state => .nil state
  | _, _, .cons first rest =>
      let macroStep := first.toMacroStep
      .cons macroStep.weight ⟨macroStep, rfl⟩ (toCorridorWalk rest)

/-- Compression preserves primitive cost across every segment. -/
theorem toCorridorWalk_cost
    (segmentation : CorridorSegmentation source target) :
    corridorWalkCost segmentation.toCorridorWalk =
      segmentation.toMirrorWalk.length := by
  induction segmentation with
  | nil => rfl
  | cons first rest ih =>
      simp only [toCorridorWalk, corridorWalkCost, toMirrorWalk,
        appendMirrorShapeWalk_length]
      change
        first.toMacroStep.weight +
            rest.toCorridorWalk.actions.sum =
          first.toWalk.length + rest.toMirrorWalk.length
      have restCost :
          rest.toCorridorWalk.actions.sum =
            rest.toMirrorWalk.length := by
        simpa [corridorWalkCost] using ih
      calc
        first.toMacroStep.weight +
              rest.toCorridorWalk.actions.sum =
            first.toWalk.length +
              rest.toCorridorWalk.actions.sum :=
          congrArg
            (fun weight => weight + rest.toCorridorWalk.actions.sum)
            (ReducedCorridorSegment.toMacroStep_weight first)
        _ = first.toWalk.length + rest.toMirrorWalk.length :=
          congrArg (fun cost => first.toWalk.length + cost) restCost

end CorridorSegmentation

/--
Compression completeness for precisely segmented reduced walks. The theorem
does not cover arbitrary walks with immediate backtracking inside a corridor:
such a walk cannot be represented by a single forced macro with the same
primitive cost.
-/
theorem corridorWalk_compressWithCost
    (walk : MirrorShapeWalk source.1 target.1)
    (segmented : CorridorSegmentationOf walk) :
    ∃ compressed : corridorTask.Walk source target,
      corridorWalkCost compressed = walk.length := by
  refine ⟨segmented.segmentation.toCorridorWalk, ?_⟩
  rw [CorridorSegmentation.toCorridorWalk_cost, segmented.realizes]

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
The expansion of a compressed reduced walk has the same primitive length as
the original mirror-quotient walk.
-/
theorem corridorWalk_compress_expand_length
    (walk : MirrorShapeWalk source.1 target.1)
    (segmented : CorridorSegmentationOf walk) :
    ∃ compressed : corridorTask.Walk source target,
      (corridorWalkExpand compressed).length = walk.length := by
  rcases corridorWalk_compressWithCost walk segmented with
    ⟨compressed, cost_eq⟩
  refine ⟨compressed, ?_⟩
  rw [corridorWalkExpand_length]
  exact cost_eq

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
