import Huarongdao.StateSpaceAnalysis
import Huarongdao.Enumeration
import Huarongdao.MirrorSearch
import Std.Data.HashMap

namespace Huarongdao
namespace StateSpace

universe u v w

/--
An executable representation of an arbitrary semantic task. `Rep` may be a
canonical concrete representative even when the semantic state is a quotient.
`Move` may retain display and lifting data even when the semantic action is
`Unit`.
-/
structure ExecutablePresentation
    {State : Type u} {Action : Type v}
    (task : Task State Action) where
  Rep : Type w
  Move : Type w
  initial : Rep
  stateOf : Rep → State
  actionOf : Move → Action
  key : Rep → String
  successors : Rep → List (Move × Rep)

namespace ExecutablePresentation

variable {State : Type u} {Action : Type v}
variable {task : Task State Action}

/-- The executable initial representative denotes the semantic root. -/
def InitialSound (presentation : ExecutablePresentation task) : Prop :=
  presentation.stateOf presentation.initial = task.initial

/-- Every emitted executable successor is a semantic task transition. -/
def SuccessorsSound (presentation : ExecutablePresentation task) : Prop :=
  ∀ {source move target},
    (move, target) ∈ presentation.successors source →
      task.step
        (presentation.stateOf source)
        (presentation.actionOf move)
        (presentation.stateOf target)

/-- Every semantic transition out of a represented state is enumerated. -/
def SuccessorsComplete (presentation : ExecutablePresentation task) : Prop :=
  ∀ {source action target},
    task.step (presentation.stateOf source) action target →
      ∃ move next,
        (move, next) ∈ presentation.successors source ∧
        presentation.actionOf move = action ∧
        presentation.stateOf next = target

/-- Equal keys identify exactly equal semantic states in the selected layer. -/
def KeyExact (presentation : ExecutablePresentation task) : Prop :=
  ∀ left right,
    presentation.key left = presentation.key right ↔
      presentation.stateOf left = presentation.stateOf right

/--
The proof obligations needed to turn a completed BFS run into a
`FiniteStateSpace`. They are kept separate from the executable data so the
queue and hash-map computation remains lightweight.
-/
structure Lawful (presentation : ExecutablePresentation task) : Prop where
  initial : presentation.InitialSound
  successors_sound : presentation.SuccessorsSound
  successors_complete : presentation.SuccessorsComplete
  key_exact : presentation.KeyExact

/-- An edge stored by the generic executable BFS engine. -/
structure IndexedEdge (presentation : ExecutablePresentation task) where
  source : Nat
  target : Nat
  move : presentation.Move

/--
Raw output of one BFS run. This is an executable artifact; semantic exactness
is established separately by replaying it into `FiniteStateSpace`.
-/
structure BfsRun (presentation : ExecutablePresentation task) where
  representatives : Array presentation.Rep
  edges : Array (IndexedEdge presentation)
  distance : Array Nat
  index : Std.HashMap String Nat

/--
One queue/hash-map BFS implementation for every state-space layer. The chosen
presentation determines whether keys denote concrete, shape, mirror, or later
quotient states.
-/
def enumerateBfs (presentation : ExecutablePresentation task) :
    BfsRun presentation := Id.run do
  let mut representatives := #[presentation.initial]
  let mut edges := #[]
  let mut distance := #[0]
  let mut known : Std.HashMap String Nat := {}
  known := known.insert (presentation.key presentation.initial) 0
  let mut cursor := 0
  while cursor < representatives.size do
    let source :=
      representatives.getD cursor presentation.initial
    let sourceDistance := distance.getD cursor 0
    for (move, targetRepresentative) in
        presentation.successors source do
      let target ←
        match known.get? (presentation.key targetRepresentative) with
        | some index =>
            pure index
        | none =>
            let index := representatives.size
            representatives :=
              representatives.push targetRepresentative
            distance := distance.push (sourceDistance + 1)
            known :=
              known.insert
                (presentation.key targetRepresentative) index
            pure index
      edges := edges.push ⟨cursor, target, move⟩
    cursor := cursor + 1
  return ⟨representatives, edges, distance, known⟩

/-- Semantic state array displayed by a completed executable run. -/
def BfsRun.states
    {presentation : ExecutablePresentation task}
    (run : BfsRun presentation) : Array State :=
  run.representatives.map presentation.stateOf

end ExecutablePresentation
end StateSpace

namespace ClassicStateSpaceKernel

/-- Label-sensitive key for the fully concrete layer. -/
def concreteKey (state : State) : String :=
  String.intercalate ","
    (Piece.all.map fun piece => toString (state.pos piece).code)

/-- Legal concrete successors carrying validity proofs for their targets. -/
def validSuccessors
    (source : ValidClassicState) :
    List (Action × ValidClassicState) :=
  (legalMoves source.1).attach.map fun move =>
    let triple := move.1
    let executed := legalMoves_sound move.2
    (⟨triple.1, triple.2.1⟩,
      ⟨triple.2.2, tryMove_preserves_validity executed⟩)

theorem validSuccessors_sound
    {source : ValidClassicState}
    {action : Action} {target : ValidClassicState}
    (member : (action, target) ∈ validSuccessors source) :
    concrete.step source action target := by
  unfold validSuccessors at member
  rw [List.mem_map] at member
  rcases member with ⟨entry, _entryMem, pairEq⟩
  cases pairEq
  exact legalMoves_sound entry.2

theorem validSuccessors_complete
    {source : ValidClassicState}
    {action : Action} {target : ValidClassicState}
    (step : concrete.step source action target) :
    ∃ move next,
      (move, next) ∈ validSuccessors source ∧
      move = action ∧ next = target := by
  refine ⟨action, target, ?_, rfl, rfl⟩
  unfold validSuccessors
  rw [List.mem_map]
  let entry :
      {move // move ∈ legalMoves source.1} :=
    ⟨(action.piece, action.direction, target.1),
      legalMoves_complete step⟩
  refine ⟨entry, by simp [entry], ?_⟩
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

/-- The exact labelled-state presentation. -/
def concretePresentation :
    StateSpace.ExecutablePresentation concrete where
  Rep := ValidClassicState
  Move := Action
  initial := ⟨classic, classic_valid⟩
  stateOf := id
  actionOf := id
  key := fun state => concreteKey state.1
  successors := validSuccessors

theorem concretePresentation_initialSound :
    concretePresentation.InitialSound :=
  rfl

theorem concretePresentation_successorsSound :
    concretePresentation.SuccessorsSound := by
  intro source move target member
  exact validSuccessors_sound member

theorem concretePresentation_successorsComplete :
    concretePresentation.SuccessorsComplete := by
  intro source action target step
  exact validSuccessors_complete step

/-- The same representatives viewed in the equal-shape quotient. -/
def shapePresentation :
    StateSpace.ExecutablePresentation shape where
  Rep := ValidClassicState
  Move := Action
  initial := ⟨classic, classic_valid⟩
  stateOf := concreteShapeObservation.classOf
  actionOf := fun _ => ()
  key := fun state => state.1.key
  successors := validSuccessors

theorem shapePresentation_initialSound :
    shapePresentation.InitialSound :=
  rfl

theorem shapePresentation_successorsSound :
    shapePresentation.SuccessorsSound := by
  intro source move target member
  exact concreteToShape.map_step
    (validSuccessors_sound member)

theorem shapePresentation_successorsComplete :
    shapePresentation.SuccessorsComplete := by
  intro source action target step
  rcases concreteShapeQuotient.liftStepFrom
      step source rfl with
    ⟨concreteAction, concreteTarget, concreteStep, targetEq⟩
  rcases validSuccessors_complete concreteStep with
    ⟨move, next, member, _moveEq, nextEq⟩
  refine ⟨move, next, member, ?_, ?_⟩
  · cases action
    rfl
  · rw [nextEq]
    exact targetEq

/-- The same representatives viewed in the equal-shape plus mirror quotient. -/
def mirrorPresentation :
    StateSpace.ExecutablePresentation mirror where
  Rep := ValidClassicState
  Move := Action
  initial := ⟨classic, classic_valid⟩
  stateOf := MirrorShapeState.ofState
  actionOf := fun _ => ()
  key := fun state => mirrorKey state.1
  successors := validSuccessors

theorem mirrorPresentation_initialSound :
    mirrorPresentation.InitialSound :=
  rfl

theorem mirrorPresentation_successorsSound :
    mirrorPresentation.SuccessorsSound := by
  intro source move target member
  exact concreteToMirror.map_step
    (validSuccessors_sound member)

theorem mirrorPresentation_successorsComplete :
    mirrorPresentation.SuccessorsComplete := by
  intro source action target step
  rcases shapeMirrorQuotient.liftStepFrom
      step (ShapeState.ofState source) rfl with
    ⟨_shapeAction, shapeTarget, shapeStep, mirrorTargetEq⟩
  rcases concreteShapeQuotient.liftStepFrom
      shapeStep source rfl with
    ⟨_concreteAction, concreteTarget, concreteStep, shapeTargetEq⟩
  rcases validSuccessors_complete concreteStep with
    ⟨move, next, member, _moveEq, nextEq⟩
  refine ⟨move, next, member, ?_, ?_⟩
  · cases action
    rfl
  · rw [nextEq]
    change
      MirrorShapeState.ofShapeState
          (ShapeState.ofState concreteTarget) =
        target
    have shapeTargetEq' :
        ShapeState.ofState concreteTarget = shapeTarget :=
      shapeTargetEq
    have mirrorTargetEq' :
        MirrorShapeState.ofShapeState shapeTarget = target :=
      mirrorTargetEq
    rw [shapeTargetEq']
    exact mirrorTargetEq'

/-- Full BFS on the labelled concrete layer. -/
def concreteBfsRun :=
  concretePresentation.enumerateBfs

/-- Full BFS on equal-shape classes, using the same generic engine. -/
def shapeBfsRun :=
  shapePresentation.enumerateBfs

/-- Full BFS on mirror classes, using the same generic engine. -/
def mirrorBfsRun :=
  mirrorPresentation.enumerateBfs

end ClassicStateSpaceKernel
end Huarongdao
