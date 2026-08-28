import Huarongdao.ClassicFullSpace
import Huarongdao.StateSpaceBfs
import Mathlib.Data.List.Sublists

namespace Huarongdao
namespace ClassicFullSpace

open StateSpace
open ClassicStateSpaceKernel

/-- A proof-facing partition of every legal equal-shape state.  The mutable
DFS implementation disappears behind these five semantic obligations. -/
structure VerifiedShapePartition where
  StateIndex : Type
  ComponentIndex : Type
  state : StateIndex → ShapeState
  classOf : StateIndex → ComponentIndex
  rank : StateIndex → Nat
  root : ComponentIndex → StateIndex
  root_component : ∀ component : ComponentIndex,
    classOf (root component) = component
  complete : ∀ node : ShapeState, ∃ index, state index = node
  state_eq_component : ∀ {left right},
    state left = state right → classOf left = classOf right
  root_or_parent : ∀ index,
    index = root (classOf index) ∨
      ∃ parent,
        rank parent < rank index ∧
        classOf parent = classOf index ∧
        shape.step (state parent) () (state index)
  closed : ∀ {index action target},
    shape.step (state index) action target →
      ∃ targetIndex,
        state targetIndex = target ∧
        classOf targetIndex = classOf index

namespace VerifiedShapePartition

variable (certificate : VerifiedShapePartition)

/-- Every indexed state is reachable from its certified component root. -/
theorem root_reachable (index : certificate.StateIndex) :
    shape.Reachable
      (certificate.state (certificate.root (certificate.classOf index)))
      (certificate.state index) := by
  induction rankValue : certificate.rank index using Nat.strong_induction_on generalizing index with
  | h rank inductionHypothesis =>
      rcases certificate.root_or_parent index with rootEq | ⟨parent, parentRank, sameComponent, edge⟩
      · rw [← rootEq]
        exact shape.reachable_refl _
      · have parentReachable :=
          inductionHypothesis (certificate.rank parent) (by simpa [rankValue] using parentRank)
            parent rfl
        have sameRoot :
            certificate.root (certificate.classOf parent) =
              certificate.root (certificate.classOf index) := by
          rw [sameComponent]
        rw [sameRoot] at parentReachable
        exact Task.reachable_trans parentReachable
          ⟨Task.Walk.cons () edge (Task.Walk.nil _)⟩

/-- Equal component labels construct an actual legal-slide walk. -/
theorem reachable_of_component_eq {source target : certificate.StateIndex}
    (sameComponent : certificate.classOf source = certificate.classOf target) :
    shape.Reachable (certificate.state source) (certificate.state target) := by
  have sourceFromRoot := certificate.root_reachable source
  have targetFromRoot := certificate.root_reachable target
  have sourceToRoot := shapeReversible.reachable_symm sourceFromRoot
  have sameRoot :
      certificate.root (certificate.classOf source) =
        certificate.root (certificate.classOf target) := by
    rw [sameComponent]
  rw [sameRoot] at sourceToRoot
  exact Task.reachable_trans sourceToRoot targetFromRoot

/-- A checked closure condition makes the component label invariant along a
semantic equal-shape walk. -/
theorem component_eq_of_walk_between
    (source : certificate.StateIndex) {walkSource target : ShapeState}
    (sourceEq : certificate.state source = walkSource)
    (walk : shape.Walk walkSource target)
    (targetIndex : certificate.StateIndex)
    (targetEq : certificate.state targetIndex = target) :
    certificate.classOf source = certificate.classOf targetIndex :=
  match walk with
  | .nil _ =>
      certificate.state_eq_component (sourceEq.trans targetEq.symm)
  | @Task.Walk.cons _ _ _ _ middle _ action edge tail => by
      have edge' : shape.step (certificate.state source) action middle := by
        rw [sourceEq]
        exact edge
      rcases certificate.closed edge' with
        ⟨middleIndex, middleEq, sameComponent⟩
      exact sameComponent.symm.trans
        (component_eq_of_walk_between
          middleIndex middleEq tail targetIndex targetEq)
termination_by walk.length

theorem component_eq_of_walk
    {source target : certificate.StateIndex}
    (walk : shape.Walk (certificate.state source) (certificate.state target)) :
    certificate.classOf source = certificate.classOf target :=
      component_eq_of_walk_between certificate source rfl walk target rfl

theorem component_eq_of_reachable
    {source target : certificate.StateIndex}
    (reachable : shape.Reachable
      (certificate.state source) (certificate.state target)) :
    certificate.classOf source = certificate.classOf target := by
  rcases reachable with ⟨walk⟩
  exact certificate.component_eq_of_walk walk

/-- The central soundness theorem: certified DFS labels coincide exactly with
the semantic reachability equivalence classes. -/
theorem component_eq_iff_reachable
    {source target : certificate.StateIndex} :
    certificate.classOf source = certificate.classOf target ↔
      shape.Reachable (certificate.state source) (certificate.state target) :=
  ⟨certificate.reachable_of_component_eq,
    certificate.component_eq_of_reachable⟩

/-- Every semantic continuous class is represented by a certified component
root. -/
theorem component_surjective :
    Function.Surjective fun index : certificate.StateIndex =>
      continuousClassOf (certificate.state index) := by
  intro componentClass
  refine Quotient.inductionOn componentClass ?_
  intro node
  rcases certificate.complete node with ⟨index, stateEq⟩
  refine ⟨index, ?_⟩
  change continuousClassOf (certificate.state index) =
    continuousClassOf node
  rw [stateEq]

def rootClass (certificate : VerifiedShapePartition) :
    certificate.ComponentIndex → ContinuousClass :=
  fun component =>
    continuousClassOf (certificate.state (certificate.root component))

theorem rootClass_surjective :
    Function.Surjective (rootClass certificate) := by
  intro classValue
  refine Quotient.inductionOn classValue ?_
  intro node
  rcases certificate.complete node with ⟨index, stateEq⟩
  refine ⟨certificate.classOf index, ?_⟩
  apply continuousClassOf_eq_iff.mpr
  change shape.Reachable
    (certificate.state (certificate.root (certificate.classOf index))) node
  simpa [stateEq] using certificate.root_reachable index

theorem rootClass_injective :
    Function.Injective (rootClass certificate) := by
  intro left right equal
  have reachable :
      shape.Reachable
        (certificate.state (certificate.root left))
        (certificate.state (certificate.root right)) :=
    continuousClassOf_eq_iff.mp equal
  have labels := certificate.component_eq_of_reachable
    (source := certificate.root left) (target := certificate.root right) reachable
  have leftRoot : certificate.classOf (certificate.root left) = left :=
    certificate.root_component left
  have rightRoot : certificate.classOf (certificate.root right) = right :=
    certificate.root_component right
  exact leftRoot.symm.trans (labels.trans rightRoot)

noncomputable def componentEquivContinuousClass :
    certificate.ComponentIndex ≃ ContinuousClass :=
  Equiv.ofBijective (rootClass certificate)
    ⟨certificate.rootClass_injective, certificate.rootClass_surjective⟩

noncomputable def continuousClassFintype
    [Fintype certificate.ComponentIndex] : Fintype ContinuousClass :=
  letI : Finite ContinuousClass :=
    Finite.of_surjective (rootClass certificate) certificate.rootClass_surjective
  Fintype.ofFinite ContinuousClass

theorem fintypeCard_continuousClass_eq
    [Fintype certificate.ComponentIndex] :
    @Fintype.card ContinuousClass (continuousClassFintype certificate) =
      Fintype.card certificate.ComponentIndex := by
  letI : Fintype ContinuousClass := continuousClassFintype certificate
  exact Fintype.card_congr certificate.componentEquivContinuousClass.symm

end VerifiedShapePartition

/-- String-key index used only as a fast candidate lookup.  Soundness never
trusts the key: `Graph.findRepresentation` rechecks the returned candidate by
constructing an explicit shape-preserving relabeling. -/
def shapeCandidateIndex (states : Array State) : Std.HashMap String Nat :=
  Id.run do
    let mut index : Std.HashMap String Nat := {}
    for stateId in List.range states.size do
      index := index.insert (states.getD stateId classic).key stateId
    return index

def representationGraph (states : Array State) : Graph where
  states := states
  edges := #[]
  distance := #[]
  index := shapeCandidateIndex states

/-- Independently replay one claimed DFS parent edge. -/
def checkParentEdge (states : Array State) (parent child : Nat) : Bool :=
  (legalMoves (states.getD parent classic)).any fun move =>
    decide (SameShape move.2.2 (states.getD child classic))

theorem checkParentEdge_sound {states : Array State} {parent child : Nat}
    (checked : checkParentEdge states parent child = true) :
    QStep (states.getD parent classic) (states.getD child classic) := by
  unfold checkParentEdge at checked
  rw [List.any_eq_true] at checked
  rcases checked with ⟨move, moveMember, represented⟩
  rcases move with ⟨piece, direction, target⟩
  exact
    ⟨piece, direction, target, legalMoves_sound moveMember,
      of_decide_eq_true represented⟩

theorem qStep_to_shape_step {source target : State}
    (sourceValid : ValidState source) (targetValid : ValidState target)
    (step : QStep source target) :
    shape.step
      (ShapeState.ofState ⟨source, sourceValid⟩) ()
      (ShapeState.ofState ⟨target, targetValid⟩) := by
  rcases step with ⟨piece, direction, actual, executed, represented⟩
  let actualValid : ValidClassicState :=
    ⟨actual, tryMove_preserves_validity executed⟩
  have concreteStep :
      concrete.step ⟨source, sourceValid⟩
        ⟨piece, direction⟩ actualValid :=
    executed
  have mapped := concreteToShape.map_step concreteStep
  have targetEq :
      ShapeState.ofState actualValid =
        ShapeState.ofState ⟨target, targetValid⟩ :=
    ShapeState.ofState_eq represented
  change
    shape.step (ShapeState.ofState ⟨source, sourceValid⟩) ()
      (ShapeState.ofState actualValid) at mapped
  rw [targetEq] at mapped
  exact mapped

/-- Check the local predecessor obligation for one DFS state. -/
def checkParentAt (states : Array State) (run : ComponentRun)
    (child : Nat) : Bool :=
  let label := run.componentOf.getD child run.roots.size
  let root := run.roots.getD label states.size
  if child == root then
    (run.parent.getD child none).isNone
  else
    match run.parent.getD child none with
    | none => false
    | some parent =>
        decide (parent < states.size) &&
        (run.componentOf.getD parent run.roots.size == label) &&
        decide
          (run.discovery.getD parent states.size <
            run.discovery.getD child states.size) &&
        checkParentEdge states parent child

def checkParents (states : Array State) (run : ComponentRun) : Bool :=
  (List.range states.size).all (checkParentAt states run)

theorem checkParentAt_sound
    {states : Array State} {run : ComponentRun} {child : Nat}
    (checked : checkParentAt states run child = true) :
    let label := run.componentOf.getD child run.roots.size
    let root := run.roots.getD label states.size
    child = root ∨
      ∃ parent,
        parent < states.size ∧
        run.componentOf.getD parent run.roots.size = label ∧
        run.discovery.getD parent states.size <
          run.discovery.getD child states.size ∧
        QStep (states.getD parent classic) (states.getD child classic) := by
  unfold checkParentAt at checked
  let label := run.componentOf.getD child run.roots.size
  let root := run.roots.getD label states.size
  change
    (if child == root then
      (run.parent.getD child none).isNone
    else
      match run.parent.getD child none with
      | none => false
      | some parent =>
          decide (parent < states.size) &&
          (run.componentOf.getD parent run.roots.size == label) &&
          decide
            (run.discovery.getD parent states.size <
              run.discovery.getD child states.size) &&
          checkParentEdge states parent child) = true at checked
  by_cases rootEq : child = root
  · exact Or.inl rootEq
  · right
    cases parentEq : run.parent.getD child none with
    | none => simp [rootEq, parentEq] at checked
    | some parent =>
        simp only [rootEq, ↓reduceIte, parentEq, decide_eq_true_eq,
          Bool.and_eq_true, beq_iff_eq] at checked
        refine ⟨parent, checked.1.1.1, checked.1.1.2,
          checked.1.2, ?_⟩
        exact checkParentEdge_sound checked.2

theorem checkParents_sound
    {states : Array State} {run : ComponentRun}
    (checked : checkParents states run = true)
    {child : Nat} (childLt : child < states.size) :
    let label := run.componentOf.getD child run.roots.size
    let root := run.roots.getD label states.size
    child = root ∨
      ∃ parent,
        parent < states.size ∧
        run.componentOf.getD parent run.roots.size = label ∧
        run.discovery.getD parent states.size <
          run.discovery.getD child states.size ∧
        QStep (states.getD parent classic) (states.getD child classic) := by
  unfold checkParents at checked
  rw [List.all_eq_true] at checked
  exact checkParentAt_sound
    (checked child (List.mem_range.mpr childLt))

/-- Check every semantic successor of one stored representative and require
the verified target representative to retain the DFS component label. -/
def checkLabelClosedAt (states : Array State) (run : ComponentRun)
    (source : Nat) : Bool :=
  let graph := representationGraph states
  (legalMoves (states.getD source classic)).all fun move =>
    match graph.findRepresentation move.2.2 with
    | none => false
    | some (target, _) =>
        run.componentOf.getD target run.roots.size ==
          run.componentOf.getD source run.roots.size

def checkLabelClosed (states : Array State) (run : ComponentRun) : Bool :=
  (List.range states.size).all (checkLabelClosedAt states run)

theorem checkLabelClosedAt_sound
    {states : Array State} {run : ComponentRun} {source : Nat}
    (checked : checkLabelClosedAt states run source = true)
    {piece : Piece} {direction : Direction} {next : State}
    (executed :
      tryMove (states.getD source classic) piece direction = some next) :
    ∃ target : Nat,
      target < states.size ∧
      SameShape next (states.getD target classic) ∧
      run.componentOf.getD target run.roots.size =
        run.componentOf.getD source run.roots.size := by
  have moveMember :
      (piece, direction, next) ∈
        legalMoves (states.getD source classic) :=
    legalMoves_complete executed
  unfold checkLabelClosedAt at checked
  rw [List.all_eq_true] at checked
  have moveChecked := checked (piece, direction, next) moveMember
  let graph := representationGraph states
  change
    (match graph.findRepresentation next with
      | none => false
      | some (target, _) =>
          run.componentOf.getD target run.roots.size ==
            run.componentOf.getD source run.roots.size) = true at moveChecked
  cases represented : graph.findRepresentation next with
  | none => simp [represented] at moveChecked
  | some result =>
      rcases result with ⟨target, relabeling⟩
      have representationSound := Graph.findRepresentation_sound represented
      refine ⟨target, representationSound.1, ?_, ?_⟩
      · rw [representationSound.2]
        exact relabel_sameShape relabeling _
      · simpa [represented] using moveChecked

theorem checkLabelClosed_sound
    {states : Array State} {run : ComponentRun}
    (checked : checkLabelClosed states run = true)
    {source : Nat} (sourceLt : source < states.size)
    {piece : Piece} {direction : Direction} {next : State}
    (executed :
      tryMove (states.getD source classic) piece direction = some next) :
    ∃ target : Nat,
      target < states.size ∧
      SameShape next (states.getD target classic) ∧
      run.componentOf.getD target run.roots.size =
        run.componentOf.getD source run.roots.size := by
  unfold checkLabelClosed at checked
  rw [List.all_eq_true] at checked
  exact checkLabelClosedAt_sound
    (checked source (List.mem_range.mpr sourceLt)) executed

/-- The two global mathematical facts, plus locally replayed DFS checks, that
turn the mutable output into a semantic partition.  `complete` is supplied by
the placement-generator completeness theorem; `shape_exact` is supplied by
the canonical-representative uniqueness proof. -/
structure ComponentRun.Lawful (states : Array State) (run : ComponentRun) : Prop where
  valid : ∀ index : Fin states.size, ValidState states[index]
  labels_bounded : ∀ index : Fin states.size,
    run.componentOf.getD index.1 run.roots.size < run.roots.size
  roots_bounded : ∀ component : Fin run.roots.size,
    run.roots.getD component.1 states.size < states.size
  roots_labelled : ∀ component : Fin run.roots.size,
    run.componentOf.getD
        (run.roots.getD component.1 states.size) run.roots.size =
      component.1
  complete : ∀ node : ShapeState,
    ∃ index : Fin states.size,
      ShapeState.ofState ⟨states[index], valid index⟩ = node
  shape_exact : ∀ {left right : Fin states.size},
    ShapeState.ofState ⟨states[left], valid left⟩ =
        ShapeState.ofState ⟨states[right], valid right⟩ →
      run.componentOf.getD left.1 run.roots.size =
        run.componentOf.getD right.1 run.roots.size
  parents_checked : checkParents states run = true
  closed_checked : checkLabelClosed states run = true

namespace ComponentRun.Lawful

variable {states : Array State} {run : ComponentRun}

/-- Check that every stored representative is a legal board.  This is kept
separate from the semantic completeness obligation: validity is a finite
executable fact, while completeness is a theorem about all quotient states. -/
def checkAllValid (states : Array State) : Bool :=
  states.all Huarongdao.valid

theorem checkAllValid_sound
    {states : Array State}
    (checked : checkAllValid states = true)
    {index : Nat} (indexLt : index < states.size) :
    ValidState (states[index]) := by
  unfold checkAllValid at checked
  exact (Array.all_eq_true.mp checked) index indexLt

def checkLabelsBounded (states : Array State) (run : ComponentRun) : Bool :=
  (List.range states.size).all fun index =>
    decide (run.componentOf.getD index run.roots.size < run.roots.size)

def checkRootsBounded (states : Array State) (run : ComponentRun) : Bool :=
  (List.range run.roots.size).all fun component =>
    decide (run.roots.getD component states.size < states.size)

def checkRootLabels (states : Array State) (run : ComponentRun) : Bool :=
  (List.range run.roots.size).all fun component =>
    decide
      (run.componentOf.getD
          (run.roots.getD component states.size) run.roots.size =
        component)

theorem checkLabelsBounded_sound
    {states : Array State} {run : ComponentRun}
    (checked : checkLabelsBounded states run = true)
    {index : Nat} (indexLt : index < states.size) :
    run.componentOf.getD index run.roots.size < run.roots.size := by
  unfold checkLabelsBounded at checked
  rw [List.all_eq_true] at checked
  exact of_decide_eq_true
    (checked index (List.mem_range.mpr indexLt))

theorem checkRootsBounded_sound
    {states : Array State} {run : ComponentRun}
    (checked : checkRootsBounded states run = true)
    {component : Nat} (componentLt : component < run.roots.size) :
    run.roots.getD component states.size < states.size := by
  unfold checkRootsBounded at checked
  rw [List.all_eq_true] at checked
  exact of_decide_eq_true
    (checked component (List.mem_range.mpr componentLt))

theorem checkRootLabels_sound
    {states : Array State} {run : ComponentRun}
    (checked : checkRootLabels states run = true)
    {component : Nat} (componentLt : component < run.roots.size) :
    run.componentOf.getD
        (run.roots.getD component states.size) run.roots.size =
      component := by
  unfold checkRootLabels at checked
  rw [List.all_eq_true] at checked
  exact of_decide_eq_true
    (checked component (List.mem_range.mpr componentLt))

/-- All finite, replayable obligations for a component run.  The checker does
not assert that the array is complete: that assertion is intentionally a
separate mathematical certificate, since it quantifies over `ShapeState`. -/
def checkFinite (states : Array State) (run : ComponentRun) : Bool :=
  checkAllValid states &&
    checkLabelsBounded states run &&
    checkRootsBounded states run &&
    checkRootLabels states run &&
    checkParents states run &&
    checkLabelClosed states run

theorem checkFinite_components
    {states : Array State} {run : ComponentRun}
    (checked : checkFinite states run = true) :
    checkAllValid states = true ∧
      checkLabelsBounded states run = true ∧
      checkRootsBounded states run = true ∧
      checkRootLabels states run = true ∧
      checkParents states run = true ∧
      checkLabelClosed states run = true := by
  unfold checkFinite at checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with
    ⟨⟨⟨⟨⟨allValid, labelsBounded⟩, rootsBounded⟩,
      rootLabels⟩, parents⟩, closed⟩
  exact ⟨allValid, labelsBounded, rootsBounded, rootLabels, parents, closed⟩

/-- Semantic obligations which cannot be reduced to a finite local replay.
They are the two inputs needed to turn `checkFinite` into `Lawful`. -/
structure SemanticCertificate
    (states : Array State) (run : ComponentRun) : Prop where
  complete : ∀
      (validAt : ∀ index : Fin states.size, ValidState states[index])
      (node : ShapeState),
    ∃ index : Fin states.size,
      ShapeState.ofState ⟨states[index], validAt index⟩ = node
  shape_exact : ∀
      (validAt : ∀ index : Fin states.size, ValidState states[index])
      {left right : Fin states.size},
      ShapeState.ofState ⟨states[left], validAt left⟩ =
          ShapeState.ofState ⟨states[right], validAt right⟩ →
        run.componentOf.getD left.1 run.roots.size =
          run.componentOf.getD right.1 run.roots.size

/-- Package the executable finite checks and the two semantic certificates
into the proof-facing DFS invariant.  This is the main soundness boundary for
the component classifier. -/
theorem lawful_of_checked
    {states : Array State} {run : ComponentRun}
    (checked : checkFinite states run = true)
    (semantic : SemanticCertificate states run) :
    run.Lawful states := by
  rcases checkFinite_components checked with
    ⟨validChecked, labelsChecked, rootsChecked,
      rootLabelsChecked, parentsChecked, closedChecked⟩
  let validAt : ∀ index : Fin states.size, ValidState states[index] :=
    fun index => checkAllValid_sound validChecked index.2
  refine {
    valid := validAt
    labels_bounded := ?_
    roots_bounded := ?_
    roots_labelled := ?_
    complete := ?_
    shape_exact := ?_
    parents_checked := parentsChecked
    closed_checked := closedChecked
  }
  · intro index
    exact checkLabelsBounded_sound labelsChecked index.2
  · intro component
    exact checkRootsBounded_sound rootsChecked component.2
  · intro component
    exact checkRootLabels_sound rootLabelsChecked component.2
  · intro node
    exact semantic.complete validAt node
  · intro left right sameState
    exact semantic.shape_exact validAt sameState

/-- A successful executable DFS checker produces the abstract certificate
whose labels are exactly semantic continuous-equivalence classes. -/
def toVerifiedShapePartition
    (lawful : run.Lawful states) : VerifiedShapePartition where
  StateIndex := Fin states.size
  ComponentIndex := Fin run.roots.size
  state := fun index =>
    ShapeState.ofState ⟨states[index], lawful.valid index⟩
  classOf := fun index =>
    ⟨run.componentOf.getD index.1 run.roots.size,
      lawful.labels_bounded index⟩
  rank := fun index => run.discovery.getD index.1 states.size
  root := fun component =>
    ⟨run.roots.getD component.1 states.size,
      lawful.roots_bounded component⟩
  root_component := by
    intro component
    apply Fin.ext
    exact lawful.roots_labelled component
  complete := lawful.complete
  state_eq_component := by
    intro left right sameState
    apply Fin.ext
    exact lawful.shape_exact sameState
  root_or_parent := by
    intro index
    rcases checkParents_sound lawful.parents_checked index.2 with
      rootEq | ⟨parent, parentLt, sameComponent, rankDecreases, parentEdge⟩
    · left
      apply Fin.ext
      exact rootEq
    · right
      let parentIndex : Fin states.size := ⟨parent, parentLt⟩
      refine ⟨parentIndex, rankDecreases, ?_, ?_⟩
      · apply Fin.ext
        exact sameComponent
      · have parentEdge' :
          QStep states[parentIndex] states[index] := by
          simpa [Array.getD, parentIndex, parentLt] using parentEdge
        exact qStep_to_shape_step
          (lawful.valid parentIndex) (lawful.valid index) parentEdge'
  closed := by
    intro index action target step
    let sourceRepresentative : ValidClassicState :=
      ⟨states[index], lawful.valid index⟩
    have representedStep :
        shape.step
          (shapePresentation.stateOf sourceRepresentative)
          action target := by
      exact step
    rcases shapePresentation_successorsComplete representedStep with
      ⟨move, next, member, _actionEq, nextEq⟩
    have concreteStep := validSuccessors_sound member
    have executed :
        tryMove (states.getD index.1 classic)
          move.piece move.direction = some next.1 := by
      change
        tryMove states[index] move.piece move.direction = some next.1
        at concreteStep
      simpa [Array.getD, index.2] using concreteStep
    rcases checkLabelClosed_sound lawful.closed_checked index.2 executed with
      ⟨targetIndex, targetLt, represented, sameComponent⟩
    let targetFin : Fin states.size := ⟨targetIndex, targetLt⟩
    refine ⟨targetFin, ?_, ?_⟩
    · have classEq :
          ShapeState.ofState next =
            ShapeState.ofState
              ⟨states[targetFin], lawful.valid targetFin⟩ := by
        apply ShapeState.ofState_eq
        simpa [Array.getD, targetFin, targetLt] using represented
      exact classEq.symm.trans nextEq
    · apply Fin.ext
      exact sameComponent

theorem component_eq_iff_reachable
    (lawful : run.Lawful states)
    {source target : Fin states.size} :
    run.componentOf.getD source.1 run.roots.size =
        run.componentOf.getD target.1 run.roots.size ↔
      shape.Reachable
        (ShapeState.ofState ⟨states[source], lawful.valid source⟩)
        (ShapeState.ofState ⟨states[target], lawful.valid target⟩) := by
  let certificate := lawful.toVerifiedShapePartition
  simpa [certificate, toVerifiedShapePartition] using
    certificate.component_eq_iff_reachable

theorem continuousClass_card_eq_898_of_certificate
    (certificate : VerifiedShapePartition)
    [Fintype certificate.ComponentIndex]
    (componentCount : Fintype.card certificate.ComponentIndex = 898) :
    @Fintype.card ContinuousClass
        (VerifiedShapePartition.continuousClassFintype certificate) = 898 :=
  certificate.fintypeCard_continuousClass_eq.trans componentCount

end ComponentRun.Lawful

end ClassicFullSpace
end Huarongdao
