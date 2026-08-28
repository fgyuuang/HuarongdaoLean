import Huarongdao.ClassicFullSpace
import Huarongdao.ClassicCertificate
import Huarongdao.MathlibSymmetry
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Huarongdao
namespace ClassicFullSpace

open StateSpace
open ClassicStateSpaceKernel

/-! ## Horizontal reflection on continuous components -/

/-- Horizontal reflection descends from shape states to reachability classes. -/
def horizontalMirrorContinuousClass : ContinuousClass → ContinuousClass :=
  Quotient.lift
    (fun state => continuousClassOf (mirrorShapeState state))
    (by
      intro source target reachable
      apply Quotient.sound
      exact
        (horizontalMirrorAction.reachable_iff
          .reflection source target).2 reachable)

@[simp] theorem horizontalMirrorContinuousClass_of
    (state : ShapeState) :
    horizontalMirrorContinuousClass (continuousClassOf state) =
      continuousClassOf (mirrorShapeState state) :=
  rfl

@[simp] theorem horizontalMirrorContinuousClass_involutive
    (component : ContinuousClass) :
    horizontalMirrorContinuousClass
        (horizontalMirrorContinuousClass component) = component := by
  induction component using Quotient.inductionOn with
  | _ state =>
      change continuousClassOf
          (mirrorShapeState (mirrorShapeState state)) =
        continuousClassOf state
      rw [mirrorShapeState_involutive]

/-- The two-element horizontal reflection group acts on continuous classes. -/
def horizontalActContinuousClass :
    HorizontalSymmetry → ContinuousClass → ContinuousClass
  | .identity, component => component
  | .reflection, component => horizontalMirrorContinuousClass component

instance horizontalSymmetryContinuousClassAction :
    MulAction HorizontalSymmetry ContinuousClass where
  smul := horizontalActContinuousClass
  one_smul := by intro component; rfl
  mul_smul := by
    intro outer inner component
    change
      horizontalActContinuousClass
          (HorizontalSymmetry.mul outer inner) component =
        horizontalActContinuousClass outer
          (horizontalActContinuousClass inner component)
    cases outer <;> cases inner
    · rfl
    · rfl
    · rfl
    · simpa only [HorizontalSymmetry.mul, horizontalActContinuousClass] using
        (horizontalMirrorContinuousClass_involutive component).symm

/-! ## An explicit two-colouring of the shape graph -/

def posWeight (position : Pos) : Nat :=
  position.x + position.y

/-- Sum of all ten top-left anchor coordinates, grouped by geometric shape. -/
def anchorWeight (state : State) : Nat :=
  posWeight (state.pos .caoCao) +
  posWeight (state.pos .guanYu) +
  ((verticalPositions state).map posWeight).sum +
  ((soldierPositions state).map posWeight).sum

theorem sameShape_anchorWeight {source target : State}
    (same : SameShape source target) :
    anchorWeight source = anchorWeight target := by
  have verticalSum := (same.2.2.1.map posWeight).sum_eq
  have soldierSum := (same.2.2.2.map posWeight).sum_eq
  simp only [anchorWeight]
  rw [same.1, same.2.1, verticalSum, soldierSum]

/-- Anchor parity is independent of labels on equal-shaped pieces. -/
def shapeParity : ShapeState → Fin 2 :=
  Quotient.lift
    (fun state => ⟨anchorWeight state.1 % 2, Nat.mod_lt _ (by omega)⟩)
    (by
      intro source target same
      apply Fin.ext
      simp only
      rw [sameShape_anchorWeight same])

private theorem tryMove_position_data
    {source target : State} {piece : Piece} {direction : Direction}
    (executed : tryMove source piece direction = some target) :
    ∃ moved,
      translated (source.pos piece) direction = some moved ∧
      target.pos piece = moved ∧
      ∀ candidate, candidate ≠ piece →
        target.pos candidate = source.pos candidate := by
  unfold tryMove at executed
  cases movedUnchecked : moveUnchecked source piece direction with
  | none => simp [movedUnchecked] at executed
  | some candidate =>
      by_cases candidateValid : valid candidate = true
      · simp [movedUnchecked, candidateValid] at executed
        subst target
        unfold moveUnchecked at movedUnchecked
        cases translatedEq : translated (source.pos piece) direction with
        | none => simp [translatedEq] at movedUnchecked
        | some moved =>
            simp [translatedEq] at movedUnchecked
            subst candidate
            refine ⟨moved, by simpa using translatedEq, ?_, ?_⟩
            · simp
            · intro other different
              simp [different]
      · simp [movedUnchecked, candidateValid] at executed

private theorem translated_weight_relation
    {position moved : Pos} {direction : Direction}
    (translatedEq : translated position direction = some moved) :
    posWeight moved + 1 = posWeight position ∨
      posWeight moved = posWeight position + 1 := by
  rcases position with ⟨x, y⟩
  cases direction with
  | up =>
      by_cases zero : y = 0
      · simp [translated, zero] at translatedEq
      · simp [translated, zero] at translatedEq
        subst moved
        left
        simp [posWeight]
        omega
  | down =>
      simp [translated] at translatedEq
      subst moved
      right
      simp [posWeight]
      omega
  | left =>
      by_cases zero : x = 0
      · simp [translated, zero] at translatedEq
      · simp [translated, zero] at translatedEq
        subst moved
        left
        simp [posWeight]
        omega
  | right =>
      simp [translated] at translatedEq
      subst moved
      right
      simp [posWeight]
      omega

theorem anchorWeight_tryMove_relation
    {source target : State} {piece : Piece} {direction : Direction}
    (executed : tryMove source piece direction = some target) :
    anchorWeight target + 1 = anchorWeight source ∨
      anchorWeight target = anchorWeight source + 1 := by
  rcases tryMove_position_data executed with
    ⟨moved, translatedEq, movedPosition, stationary⟩
  have weightRelation := translated_weight_relation translatedEq
  cases piece <;>
    simp [anchorWeight, verticalPositions, soldierPositions,
      movedPosition, stationary, posWeight] at weightRelation ⊢ <;>
    omega

theorem anchorParity_flips_of_tryMove
    {source target : State} {piece : Piece} {direction : Direction}
    (executed : tryMove source piece direction = some target) :
    anchorWeight source % 2 ≠ anchorWeight target % 2 := by
  have relation := anchorWeight_tryMove_relation executed
  omega

theorem shapeParity_ne_of_step {source target : ShapeState}
    (step : shape.step source () target) :
    shapeParity source ≠ shapeParity target := by
  have shapeStep : ShapeStep source target :=
    (shapeStep_iff_observationStep source target).mpr step
  rcases shapeStep with
    ⟨sourceState, targetState, sourceEq, targetEq,
      ⟨action, executed⟩⟩
  rw [← sourceEq, ← targetEq]
  intro equalParity
  have equalValue := congrArg Fin.val equalParity
  exact anchorParity_flips_of_tryMove executed equalValue

/-- A concrete Mathlib colouring certificate for the full equal-shape graph. -/
def shapeParityColoring :
    (shape.simpleGraph shapeReversible).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk shapeParity (by
    intro source target adjacent
    rcases adjacent.1 with ⟨label, step⟩
    cases label
    exact shapeParity_ne_of_step step)

/-- The full equal-shape state graph is bipartite. -/
theorem shapeGraph_isBipartite :
    (shape.simpleGraph shapeReversible).IsBipartite :=
  ⟨shapeParityColoring⟩

/-! ## Vertical reflection of the geometric state graph -/

/-- Reflection in the horizontal midline of the `4 × 5` board. -/
def verticalMirrorPos (piece : Piece) (position : Pos) : Pos :=
  ⟨position.x, 5 - (position.y + piece.shape.height)⟩

def verticalMirrorState (state : State) : State :=
  State.ofFn fun piece => verticalMirrorPos piece (state.pos piece)

@[simp] theorem verticalMirrorState_pos (state : State) (piece : Piece) :
    (verticalMirrorState state).pos piece =
      verticalMirrorPos piece (state.pos piece) := by
  simp [verticalMirrorState]

def verticalMirrorDirection : Direction → Direction
  | .up => .down
  | .down => .up
  | .left => .left
  | .right => .right

@[simp] theorem verticalMirrorDirection_involutive (direction : Direction) :
    verticalMirrorDirection (verticalMirrorDirection direction) = direction := by
  cases direction <;> rfl

def VerticallyBounded (state : State) : Prop :=
  ∀ piece, (state.pos piece).y + piece.shape.height ≤ 5

theorem valid_verticallyBounded {state : State} (validState : ValidState state) :
    VerticallyBounded state := by
  intro piece
  unfold ValidState valid at validState
  rw [Bool.and_eq_true] at validState
  rcases validState with ⟨bounds, _⟩
  unfold inBounds at bounds
  rw [Bool.and_eq_true] at bounds
  rcases bounds with ⟨_, allBounds⟩
  have pieceBounds :=
    (List.all_eq_true.mp allBounds) piece (Piece.mem_all piece)
  rw [Bool.and_eq_true] at pieceBounds
  exact of_decide_eq_true pieceBounds.2

theorem verticalMirror_twice (state : State)
    (bounded : VerticallyBounded state) :
    ObservationalEq (verticalMirrorState (verticalMirrorState state)) state := by
  intro piece
  have pieceBound := bounded piece
  rcases positionEq : state.pos piece with ⟨x, y⟩
  simp only [verticalMirrorState_pos, verticalMirrorPos, positionEq] at pieceBound ⊢
  congr
  omega

theorem verticalMirror_preserves_verticallyBounded {state : State}
    (bounded : VerticallyBounded state) :
    VerticallyBounded (verticalMirrorState state) := by
  intro piece
  have pieceBound := bounded piece
  rcases positionEq : state.pos piece with ⟨x, y⟩
  simp only [verticalMirrorState_pos, verticalMirrorPos, positionEq] at pieceBound ⊢
  omega

def verticalMirrorCell (position : Pos) : Pos :=
  ⟨position.x, 4 - position.y⟩

private theorem range_two_vertical : List.range 2 = [0, 1] := by decide

theorem occupiedCells_verticalMirror_perm {state : State}
    (bounded : VerticallyBounded state) (piece : Piece) :
    (occupiedCells (verticalMirrorState state) piece).Perm
      ((occupiedCells state piece).map verticalMirrorCell) := by
  have pieceBound := bounded piece
  rcases positionEq : state.pos piece with ⟨x, y⟩
  cases piece <;>
    simp [occupiedCells, verticalMirrorState_pos, verticalMirrorPos,
      verticalMirrorCell, Piece.shape, positionEq] at pieceBound ⊢
  all_goals simp [range_two_vertical, verticalMirrorCell]
  case caoCao =>
    have yStep : 3 - y + 1 = 4 - y := by omega
    rw [yStep]
    change
      ([Pos.mk x (3 - y), Pos.mk (x + 1) (3 - y)] ++
        [Pos.mk x (4 - y), Pos.mk (x + 1) (4 - y)]).Perm
      ([Pos.mk x (4 - y), Pos.mk (x + 1) (4 - y)] ++
        [Pos.mk x (3 - y), Pos.mk (x + 1) (3 - y)])
    exact List.perm_append_comm
  case zhangFei =>
    have yStep : 3 - y + 1 = 4 - y := by omega
    rw [yStep]
    exact List.Perm.swap _ _ []
  case zhaoYun =>
    have yStep : 3 - y + 1 = 4 - y := by omega
    rw [yStep]
    exact List.Perm.swap _ _ []
  case maChao =>
    have yStep : 3 - y + 1 = 4 - y := by omega
    rw [yStep]
    exact List.Perm.swap _ _ []
  case huangZhong =>
    have yStep : 3 - y + 1 = 4 - y := by omega
    rw [yStep]
    exact List.Perm.swap _ _ []

theorem occupiedCell_y_lt {state : State} {piece : Piece} {cell : Pos}
    (bounded : VerticallyBounded state)
    (member : cell ∈ occupiedCells state piece) :
    cell.y < 5 := by
  have pieceBound := bounded piece
  simp only [occupiedCells, List.mem_flatMap, List.mem_map] at member
  rcases member with ⟨dy, dyMember, dx, dxMember, cellEq⟩
  subst cell
  have dyLt := List.mem_range.mp dyMember
  simp only
  omega

theorem verticalMirrorCell_injective_of_lt {left right : Pos}
    (leftBound : left.y < 5) (rightBound : right.y < 5)
    (equal : verticalMirrorCell left = verticalMirrorCell right) :
    left = right := by
  rcases left with ⟨leftX, leftY⟩
  rcases right with ⟨rightX, rightY⟩
  simp only [verticalMirrorCell] at equal
  have xEqual := congrArg Pos.x equal
  have yEqual := congrArg Pos.y equal
  simp only at leftBound rightBound xEqual yEqual
  congr <;> omega

theorem inBounds_verticalMirror {state : State}
    (bounds : inBounds state = true) :
    inBounds (verticalMirrorState state) = true := by
  unfold inBounds at bounds ⊢
  rw [Bool.and_eq_true] at bounds ⊢
  rcases bounds with ⟨_, allBounds⟩
  constructor
  · simp [verticalMirrorState, State.ofFn, Piece.all]
  · apply List.all_eq_true.mpr
    intro piece pieceMember
    have original :=
      (List.all_eq_true.mp allBounds) piece pieceMember
    rw [Bool.and_eq_true] at original ⊢
    rcases original with ⟨xBound, yBound⟩
    constructor
    · simpa [verticalMirrorState_pos, verticalMirrorPos] using xBound
    · have yBoundProp := of_decide_eq_true yBound
      rcases positionEq : state.pos piece with ⟨x, y⟩
      cases piece <;>
        simp [verticalMirrorState_pos, verticalMirrorPos,
          Piece.shape, positionEq] at yBoundProp ⊢ <;>
        omega

theorem noOverlap_verticalMirror {state : State}
    (bounded : VerticallyBounded state)
    (noOverlapState : noOverlap state = true) :
    noOverlap (verticalMirrorState state) = true := by
  unfold noOverlap at noOverlapState ⊢
  apply List.all_eq_true.mpr
  intro piece pieceMember
  apply List.all_eq_true.mpr
  intro other otherMember
  by_cases samePiece : piece = other
  · subst other
    cases piece <;> rfl
  · have original :=
      (List.all_eq_true.mp
        ((List.all_eq_true.mp noOverlapState) piece pieceMember))
        other otherMember
    have pieceNeBool : (piece == other) = false := by
      cases piece <;> cases other <;> first | contradiction | rfl
    rw [pieceNeBool] at original ⊢
    simp only [Bool.false_or] at original ⊢
    apply List.all_eq_true.mpr
    intro left leftMember
    apply List.all_eq_true.mpr
    intro right rightMember
    have leftPerm := occupiedCells_verticalMirror_perm bounded piece
    have rightPerm := occupiedCells_verticalMirror_perm bounded other
    have leftMap :
        left ∈ (occupiedCells state piece).map verticalMirrorCell :=
      (leftPerm.mem_iff).mp leftMember
    have rightMap :
        right ∈ (occupiedCells state other).map verticalMirrorCell :=
      (rightPerm.mem_iff).mp rightMember
    rcases List.mem_map.mp leftMap with ⟨left0, left0Member, rfl⟩
    rcases List.mem_map.mp rightMap with ⟨right0, right0Member, rfl⟩
    have unequalBool :=
      (List.all_eq_true.mp
        ((List.all_eq_true.mp original) left0 left0Member))
        right0 right0Member
    have unequal : left0 ≠ right0 := bne_iff_ne.mp unequalBool
    have mirroredUnequal :
        verticalMirrorCell left0 ≠ verticalMirrorCell right0 := by
      intro equal
      exact unequal (verticalMirrorCell_injective_of_lt
        (occupiedCell_y_lt bounded left0Member)
        (occupiedCell_y_lt bounded right0Member) equal)
    exact bne_iff_ne.mpr mirroredUnequal

theorem valid_verticalMirror {state : State} (validState : ValidState state) :
    ValidState (verticalMirrorState state) := by
  have bounded := valid_verticallyBounded validState
  unfold ValidState valid at validState ⊢
  rw [Bool.and_eq_true] at validState ⊢
  exact ⟨inBounds_verticalMirror validState.1,
    noOverlap_verticalMirror bounded validState.2⟩

theorem verticalMirror_translated_of_some
    {piece : Piece} {position moved : Pos} {direction : Direction}
    (sourceBound : position.y + piece.shape.height ≤ 5)
    (targetBound : moved.y + piece.shape.height ≤ 5)
    (translatedEq : translated position direction = some moved) :
    translated (verticalMirrorPos piece position)
        (verticalMirrorDirection direction) =
      some (verticalMirrorPos piece moved) := by
  cases direction with
  | up =>
      rcases position with ⟨x, y⟩
      by_cases zero : y = 0
      · simp [translated, zero] at translatedEq
      · simp [translated, zero] at translatedEq
        subst moved
        cases piece <;>
          simp [translated, verticalMirrorPos, verticalMirrorDirection,
            Piece.shape] at sourceBound targetBound ⊢ <;>
          omega
  | down =>
      rcases position with ⟨x, y⟩
      simp [translated] at translatedEq
      subst moved
      cases piece <;>
        simp [translated, verticalMirrorPos, verticalMirrorDirection,
          Piece.shape] at sourceBound targetBound ⊢ <;>
        omega
  | left =>
      rcases position with ⟨x, y⟩
      by_cases zero : x = 0
      · simp [translated, zero] at translatedEq
      · simp [translated, zero] at translatedEq
        subst moved
        simp [translated, zero, verticalMirrorPos,
          verticalMirrorDirection]
  | right =>
      rcases position with ⟨x, y⟩
      simp [translated] at translatedEq
      subst moved
      simp [translated, verticalMirrorPos, verticalMirrorDirection]

theorem verticalMirror_moveUnchecked
    {source target : State} {piece : Piece} {direction : Direction}
    (sourceBound : VerticallyBounded source)
    (targetBound : VerticallyBounded target)
    (executed : moveUnchecked source piece direction = some target) :
    moveUnchecked (verticalMirrorState source) piece
        (verticalMirrorDirection direction) =
      some (verticalMirrorState target) := by
  unfold moveUnchecked at executed
  cases translatedEq : translated (source.pos piece) direction with
  | none => simp [translatedEq] at executed
  | some moved =>
      simp [translatedEq] at executed
      subst target
      have movedBound : moved.y + piece.shape.height ≤ 5 := by
        have pieceBound := targetBound piece
        simpa [State.ofFn_pos] using pieceBound
      have mirroredTranslation :=
        verticalMirror_translated_of_some
          (sourceBound piece) movedBound translatedEq
      unfold moveUnchecked
      simp [verticalMirrorState_pos, mirroredTranslation]
      congr 1
      ext other
      by_cases same : other = piece <;>
        simp [State.ofFn_pos, same]

/-- Legal primitive moves commute with vertical reflection. -/
theorem verticalMirror_tryMove
    {source target : State} {piece : Piece} {direction : Direction}
    (sourceValid : ValidState source)
    (executed : tryMove source piece direction = some target) :
    tryMove (verticalMirrorState source) piece
        (verticalMirrorDirection direction) =
      some (verticalMirrorState target) := by
  have targetValid : ValidState target := tryMove_preserves_validity executed
  have sourceBound := valid_verticallyBounded sourceValid
  have targetBound := valid_verticallyBounded targetValid
  unfold tryMove at executed ⊢
  cases movedEq : moveUnchecked source piece direction with
  | none => simp [movedEq] at executed
  | some candidate =>
      by_cases candidateValid : valid candidate = true
      · simp [movedEq, candidateValid] at executed
        subst target
        have mirroredMove :=
          verticalMirror_moveUnchecked sourceBound targetBound movedEq
        have mirroredValid : valid (verticalMirrorState candidate) = true :=
          valid_verticalMirror candidateValid
        simp [mirroredMove, mirroredValid]
      · simp [movedEq, candidateValid] at executed

/-- Vertical reflection respects the equal-shape quotient. -/
theorem verticalMirror_sameShape {source target : State}
    (same : SameShape source target) :
    SameShape (verticalMirrorState source) (verticalMirrorState target) := by
  rcases same with ⟨cao, guan, vertical, soldiers⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [verticalMirrorState_pos]
    rw [cao]
  · simp only [verticalMirrorState_pos]
    rw [guan]
  · simpa [verticalPositions, verticalMirrorState_pos,
      verticalMirrorPos, Piece.shape] using
      vertical.map (fun position : Pos =>
        (Pos.mk position.x (3 - position.y)))
  · simpa [soldierPositions, verticalMirrorState_pos,
      verticalMirrorPos, Piece.shape, verticalMirrorCell] using
      soldiers.map verticalMirrorCell

def verticalMirrorValidState (state : ValidClassicState) : ValidClassicState :=
  ⟨verticalMirrorState state.1, valid_verticalMirror state.2⟩

/-- The vertical board reflection induced on equal-shape states. -/
def verticalMirrorShapeState (state : ShapeState) : ShapeState :=
  Quotient.liftOn state
    (fun representative => ShapeState.ofState
      (verticalMirrorValidState representative))
    (by
      intro source target same
      exact Quotient.sound (verticalMirror_sameShape same))

@[simp] theorem verticalMirrorShapeState_ofState
    (state : ValidClassicState) :
    verticalMirrorShapeState (ShapeState.ofState state) =
      ShapeState.ofState (verticalMirrorValidState state) :=
  rfl

@[simp] theorem verticalMirrorShapeState_involutive (state : ShapeState) :
    verticalMirrorShapeState (verticalMirrorShapeState state) = state := by
  refine Quotient.inductionOn state ?_
  intro representative
  apply Quotient.sound
  exact observationalEq_sameShape
    (verticalMirror_twice representative.1
      (valid_verticallyBounded representative.2))

theorem shapeStep_verticalMirror {source target : ShapeState}
    (step : ShapeStep source target) :
    ShapeStep (verticalMirrorShapeState source)
      (verticalMirrorShapeState target) := by
  rcases step with
    ⟨sourceState, targetState, sourceEq, targetEq,
      ⟨action, executed⟩⟩
  refine ⟨verticalMirrorValidState sourceState,
    verticalMirrorValidState targetState, ?_, ?_, ?_⟩
  · simpa using congrArg verticalMirrorShapeState sourceEq
  · simpa using congrArg verticalMirrorShapeState targetEq
  · exact ⟨⟨action.piece, verticalMirrorDirection action.direction⟩,
      verticalMirror_tryMove sourceState.2 executed⟩

theorem shapeReachable_verticalMirror
    {source target : ShapeState}
    (reachable : shape.Reachable source target) :
    shape.Reachable (verticalMirrorShapeState source)
      (verticalMirrorShapeState target) := by
  rcases reachable with ⟨walk⟩
  refine ⟨?_⟩
  induction walk with
  | nil => exact .nil _
  | cons label first tail inductionHypothesis =>
      cases label
      exact .cons ()
        ((shapeStep_iff_observationStep _ _).mp
          (shapeStep_verticalMirror
            ((shapeStep_iff_observationStep _ _).mpr first)))
        inductionHypothesis

/-- Vertical reflection also permutes continuous components. -/
def verticalMirrorContinuousClass : ContinuousClass → ContinuousClass :=
  Quotient.lift
    (fun state => continuousClassOf (verticalMirrorShapeState state))
    (by
      intro source target reachable
      exact Quotient.sound (shapeReachable_verticalMirror reachable))

@[simp] theorem verticalMirrorContinuousClass_of (state : ShapeState) :
    verticalMirrorContinuousClass (continuousClassOf state) =
      continuousClassOf (verticalMirrorShapeState state) :=
  rfl

@[simp] theorem verticalMirrorContinuousClass_involutive
    (component : ContinuousClass) :
    verticalMirrorContinuousClass
        (verticalMirrorContinuousClass component) = component := by
  induction component using Quotient.inductionOn with
  | _ state =>
      change continuousClassOf
          (verticalMirrorShapeState (verticalMirrorShapeState state)) =
        continuousClassOf state
      rw [verticalMirrorShapeState_involutive]

/-! ## Executable component-action checker -/

/-- A component partition retaining the class identifier of every state. -/
structure ComponentLabeling where
  index : Std.HashMap Nat Nat
  labels : Array Nat
  representatives : Array State
  sizes : Array Nat
  closed : Bool

/-- Single-pass DFS with a stable component number. -/
def componentLabelingOf (states : Array State) : ComponentLabeling := Id.run do
  let index := placementIndex states
  let sentinel := states.size
  let mut labels := Array.replicate states.size sentinel
  let mut representatives : Array State := #[]
  let mut sizes : Array Nat := #[]
  let mut closed := true
  for candidateId in List.range states.size do
    if labels.getD candidateId sentinel = sentinel then
      let componentId := representatives.size
      let candidate := states.getD candidateId classic
      let mut stack : Array Nat := #[candidateId]
      let mut size := 0
      labels := labels.set! candidateId componentId
      while 0 < stack.size do
        let currentId := stack.getD (stack.size - 1) candidateId
        stack := stack.pop
        let current := states.getD currentId classic
        let occupancy := occupancyTable current
        size := size + 1
        for piece in Piece.all do
          for direction in Direction.all do
            match locallyLegalMove current occupancy piece direction with
            | none => pure ()
            | some target =>
                match index.get? (placementCode target) with
                | none => closed := false
                | some targetId =>
                    let targetLabel := labels.getD targetId sentinel
                    if targetLabel = sentinel then
                      labels := labels.set! targetId componentId
                      stack := stack.push targetId
                    else if targetLabel != componentId then
                      closed := false
      representatives := representatives.push candidate
      sizes := sizes.push size
  return ⟨index, labels, representatives, sizes, closed⟩

def componentIdOfStateIn?
    (labeling : ComponentLabeling) (state : State) : Option Nat := do
  let stateId ← labeling.index.get? (placementCode state)
  labeling.labels[stateId]?

/-- Component map induced by a raw geometric transformation. -/
def componentMapOf (labeling : ComponentLabeling)
    (transform : State → State) : Array Nat :=
  labeling.representatives.map fun representative =>
    (componentIdOfStateIn? labeling (transform representative)).getD
      labeling.representatives.size

/-- Check that a state transformation respects every computed component. -/
def checkComponentMap (states : Array State) (labeling : ComponentLabeling)
    (transform : State → State)
    (componentMap : Array Nat) : Bool :=
  (List.range states.size).all fun stateId =>
    let source := states.getD stateId classic
    match labeling.index.get? (placementCode (transform source)) with
    | none => false
    | some targetId =>
        let sourceComponent :=
          labeling.labels.getD stateId states.size
        let targetComponent :=
          labeling.labels.getD targetId states.size
        componentMap.getD sourceComponent states.size =
          targetComponent

def fixedComponentCount (componentMap : Array Nat) : Nat :=
  (List.range componentMap.size).countP fun componentId =>
    componentMap.getD componentId componentMap.size = componentId

/-- Number of unordered orbits of a checked involution on component ids. -/
def componentOrbitCount (componentMap : Array Nat) : Nat := Id.run do
  let count := componentMap.size
  let mut orbitKeys : Std.HashSet Nat := {}
  for source in List.range count do
    let target := componentMap.getD source count
    let low := min source target
    let high := max source target
    orbitKeys := orbitKeys.insert (low * (count + 1) + high)
  return orbitKeys.size

structure ComponentSymmetryAnalysis where
  labeling : ComponentLabeling
  horizontalMap : Array Nat
  verticalMap : Array Nat
  horizontalMapSound : Bool
  verticalMapSound : Bool
  horizontalFixedCount : Nat
  horizontalOrbitCount : Nat
  classicId : Nat
  verticalClassicId : Nat
  classicSize : Nat
  verticalClassicSize : Nat

def analyzeComponentSymmetries : ComponentSymmetryAnalysis :=
  let states := allShapeStates
  let labeling := componentLabelingOf states
  let horizontalMap := componentMapOf labeling mirrorState
  let verticalMap := componentMapOf labeling verticalMirrorState
  let classicId :=
    (componentIdOfStateIn? labeling classic).getD
      labeling.representatives.size
  let verticalClassicId :=
    (componentIdOfStateIn? labeling (verticalMirrorState classic)).getD
      labeling.representatives.size
  {
    labeling := labeling
    horizontalMap := horizontalMap
    verticalMap := verticalMap
    horizontalMapSound :=
      checkComponentMap states labeling mirrorState horizontalMap
    verticalMapSound :=
      checkComponentMap states labeling verticalMirrorState verticalMap
    horizontalFixedCount := fixedComponentCount horizontalMap
    horizontalOrbitCount := componentOrbitCount horizontalMap
    classicId := classicId
    verticalClassicId := verticalClassicId
    classicSize := labeling.sizes.getD classicId 0
    verticalClassicSize := labeling.sizes.getD verticalClassicId 0
  }

def componentLabeling : ComponentLabeling :=
  analyzeComponentSymmetries.labeling

def horizontalComponentMap : Array Nat :=
  analyzeComponentSymmetries.horizontalMap

def verticalComponentMap : Array Nat :=
  analyzeComponentSymmetries.verticalMap

def horizontalComponentMapSoundCheck : Bool :=
  analyzeComponentSymmetries.horizontalMapSound

def verticalComponentMapSoundCheck : Bool :=
  analyzeComponentSymmetries.verticalMapSound

def classicComponentId : Nat :=
  analyzeComponentSymmetries.classicId

def verticalClassicComponentId : Nat :=
  analyzeComponentSymmetries.verticalClassicId

def componentSize (componentId : Nat) : Nat :=
  componentLabeling.sizes.getD componentId 0

/-- Numerical claims for both reflection actions on the computed partition. -/
def componentSymmetryClaims : Prop :=
  let result := analyzeComponentSymmetries
  result.labeling.closed = true ∧
  result.labeling.representatives.size = 898 ∧
  result.labeling.labels.size = 65880 ∧
  result.horizontalMapSound = true ∧
  result.verticalMapSound = true ∧
  fixedComponentCount result.horizontalMap = 20 ∧
  componentOrbitCount result.horizontalMap = 459 ∧
  result.classicId ≠ result.verticalClassicId ∧
  result.labeling.sizes.getD result.classicId 0 = 25955 ∧
  result.labeling.sizes.getD result.verticalClassicId 0 = 25955 ∧
  result.verticalMap.getD result.classicId 898 =
    result.verticalClassicId ∧
  result.verticalMap.getD result.verticalClassicId 898 = result.classicId

instance componentSymmetryClaimsDecidable :
    Decidable componentSymmetryClaims := by
  unfold componentSymmetryClaims
  infer_instance

def checkComponentSymmetries : Bool :=
  decide componentSymmetryClaims

/-! ## A finite non-reachability certificate for the vertical reflection -/

def classicShapeState : ShapeState :=
  ShapeState.ofState ⟨classic, classic_valid⟩

def verticalClassicState : State :=
  verticalMirrorState classic

theorem verticalClassicState_valid : ValidState verticalClassicState :=
  valid_verticalMirror classic_valid

def verticalClassicShapeState : ShapeState :=
  ShapeState.ofState ⟨verticalClassicState, verticalClassicState_valid⟩

def checkVerticalClassicSeparated : Bool :=
  (List.range classicQuotientGraph.states.size).all fun node =>
    !(decide (SameShape verticalClassicState
      (classicQuotientGraph.states.getD node classic)))

theorem checkVerticalClassicSeparated_sound
    (checked : checkVerticalClassicSeparated = true)
    (node : Nat) (nodeLt : node < classicQuotientGraph.states.size) :
    ¬SameShape verticalClassicState
      (classicQuotientGraph.states.getD node classic) := by
  unfold checkVerticalClassicSeparated at checked
  have nodeChecked :=
    (List.all_eq_true.mp checked) node (List.mem_range.mpr nodeLt)
  simpa [Array.getD] using nodeChecked

private def validClassicWalkToPath :
    validClassicTask.Walk source target → Path source.1 target.1
  | .nil state => .nil state.1
  | .cons action first tail =>
      .cons action first (validClassicWalkToPath tail)

private theorem represents_sameShape
    {state : State} {node : Fin classicQuotientGraph.states.size}
    (represented : classicQuotientGraph.Represents state node) :
    SameShape state
      (classicQuotientGraph.states.getD node classic) := by
  rcases represented with ⟨relabeling, observational⟩
  exact sameShape_trans
    (observationalEq_sameShape observational)
    (relabel_sameShape relabeling _)

private theorem classicQuotientChecks :
    decide (0 < classicQuotientGraph.states.size) = true ∧
    checkStartRepresentation classicQuotientGraph classic = true ∧
    decide (classicQuotientGraph.distance.getD 0 0 = 0) = true ∧
    checkRelabeledClosed classicQuotientGraph = true ∧
    checkIndexedGoalLowerBound classicQuotientGraph 116 = true := by
  have checked := classicQuotientLowerBound_checked
  unfold checkQuotientLowerBound at checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with ⟨⟨⟨⟨size, start⟩, root⟩, closed⟩, goals⟩
  exact ⟨size, start, root, closed, goals⟩

/-- The classic certificate with its concrete finite node type exposed. -/
private def explicitClassicQuotientCertificate :
    QuotientLowerBoundCertificate classic 116 :=
  classicQuotientGraph.quotientLowerBoundCertificate classic 116
    (of_decide_eq_true classicQuotientChecks.1)
    classicQuotientChecks.2.1
    (of_decide_eq_true classicQuotientChecks.2.2.1)
    classicQuotientChecks.2.2.2.1
    classicQuotientChecks.2.2.2.2

/--
Once the finite classic component is independently checked not to contain the
vertical reflection, its existing closed quotient certificate proves genuine
semantic non-reachability in `ShapeState`.
-/
theorem not_continuousEquivalent_classic_verticalMirror_of_check
    (separated : checkVerticalClassicSeparated = true) :
    ¬ContinuousEquivalent classicShapeState verticalClassicShapeState := by
  intro reachable
  rcases reachable with ⟨shapeWalk⟩
  rcases shapeTask_liftWalkWithLength shapeWalk
      ⟨classic, classic_valid⟩ rfl with
    ⟨target, concreteWalk, _, targetClass⟩
  let rawPath : Path classic target.1 :=
    validClassicWalkToPath concreteWalk
  rcases explicitClassicQuotientCertificate.path_potential_le rawPath with
    ⟨node, represented, _⟩
  change Fin classicQuotientGraph.states.size at node
  change classicQuotientGraph.Represents target.1 node at represented
  have targetSameVertical : SameShape target.1 verticalClassicState :=
    ShapeState.sameShape_of_ofState_eq (by
      simpa [verticalClassicShapeState] using targetClass)
  have targetSameGraph := represents_sameShape represented
  have verticalSameGraph :
      SameShape verticalClassicState
        (classicQuotientGraph.states.getD node classic) :=
    sameShape_trans (sameShape_symm targetSameVertical) targetSameGraph
  exact
    (checkVerticalClassicSeparated_sound separated node node.isLt)
      verticalSameGraph

end ClassicFullSpace
end Huarongdao
