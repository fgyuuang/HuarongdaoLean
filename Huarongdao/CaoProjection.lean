import Huarongdao.StateSpaceKernel

namespace Huarongdao
namespace ClassicStateSpaceKernel

/-- The coarse observable used by the frontend's "track Cao Cao" view. -/
def caoPosition (state : ValidClassicState) : Pos :=
  state.1.pos .caoCao

/-- A representative-independent coordinate for Cao Cao modulo horizontal
    reflection. For a valid board, `x = 0` and `x = 2` share the same key,
    while the central position `x = 1` is fixed. -/
def canonicalCaoPosition (position : Pos) : Pos :=
  ⟨min position.x (2 - position.x), position.y⟩

/-- Cao Cao's position modulo the horizontal reflection symmetry. -/
def caoPositionOrbit (state : ValidClassicState) : Pos :=
  canonicalCaoPosition (caoPosition state)

/-- The orbit coordinate is unchanged when the complete board is mirrored. -/
@[simp] theorem caoPositionOrbit_mirror (state : ValidClassicState) :
    caoPositionOrbit (mirrorValidState state) =
      caoPositionOrbit state := by
  have horizontalBound :=
    valid_horizontallyBounded state.2 .caoCao
  rcases positionEq : state.1.pos .caoCao with ⟨x, y⟩
  have xBound : x ≤ 2 := by
    simpa [positionEq, Piece.shape] using horizontalBound
  have mirrorX : 4 - (x + 2) = 2 - x := by omega
  have subtractTwice : 2 - (2 - x) = x := by omega
  simp [
    caoPositionOrbit,
    canonicalCaoPosition,
    caoPosition,
    mirrorValidState,
    mirrorState_pos,
    mirrorPos,
    Piece.shape,
    positionEq,
    mirrorX,
    subtractTwice
  ]
  exact Nat.min_comm _ _

/-- Two legal boards are observationally identical when Cao Cao occupies the
    same top-left board coordinate. Other pieces remain deliberately hidden. -/
def SameCaoPosition (source target : ValidClassicState) : Prop :=
  caoPosition source = caoPosition target

def sameCaoPositionSetoid : Setoid ValidClassicState where
  r := SameCaoPosition
  iseqv := {
    refl := fun _ => rfl
    symm := Eq.symm
    trans := Eq.trans
  }

/-- Cao Cao position is a sound observation because the classic goal depends
    only on Cao Cao's coordinate. This is intentionally not packaged as a
    `BisimulationQuotient`: equal positions can expose different future moves. -/
def caoPositionObservation :
    StateSpace.Observation concrete where
  setoid := sameCaoPositionSetoid
  goal_iff := by
    intro source target samePosition
    change
      source.1.pos .caoCao = target.1.pos .caoCao
        at samePosition
    change goal source.1 = true ↔ goal target.1 = true
    unfold goal
    rw [samePosition]

abbrev CaoPositionState :=
  caoPositionObservation.Node

/-- Relational-image task induced by observing only Cao Cao's position. -/
def caoPositionTask :
    StateSpace.Task CaoPositionState Unit :=
  caoPositionObservation.quotientTask

/-- Every concrete move and walk projects to the Cao-position observation. -/
def concreteToCaoPosition :
    StateSpace.Task.Hom concrete caoPositionTask :=
  caoPositionObservation.projectionHom

@[simp] theorem caoPosition_class_eq
    {source target : ValidClassicState} :
    caoPositionObservation.classOf source =
        caoPositionObservation.classOf target ↔
      caoPosition source = caoPosition target := by
  constructor
  · exact Quotient.exact
  · intro samePosition
    apply Quotient.sound
    exact samePosition

@[simp] theorem caoPosition_goal_iff
    (state : ValidClassicState) :
    caoPositionTask.goal
        (caoPositionObservation.classOf state) ↔
      concrete.goal state :=
  Iff.rfl

theorem concreteWalk_projectsToCaoPosition
    (walk : concrete.Walk source target) :
    (concreteToCaoPosition.mapWalk walk).length = walk.length :=
  concreteToCaoPosition.mapWalk_length walk

/-- A move of another piece leaves the Cao-position observation unchanged. -/
theorem caoPosition_eq_of_step_other
    {source target : ValidClassicState} {action : Action}
    (step : concrete.step source action target)
    (other : action.piece ≠ .caoCao) :
    caoPosition source = caoPosition target := by
  have targetPosition :=
    tryMove_pos
      (s := source.1) (next := target.1)
      (p := action.piece) (q := .caoCao)
      (d := action.direction) step
  change source.1.pos .caoCao = target.1.pos .caoCao
  rw [targetPosition, if_neg (Ne.symm other)]

/-- Therefore every non-loop edge visible in the Cao-position projection is
    induced by an actual move of Cao Cao, matching the frontend edge filter. -/
theorem action_eq_caoCao_of_caoPosition_ne
    {source target : ValidClassicState} {action : Action}
    (step : concrete.step source action target)
    (changes : caoPosition source ≠ caoPosition target) :
    action.piece = .caoCao := by
  exact Classical.byContradiction fun other =>
    changes (caoPosition_eq_of_step_other step other)

/-- Cao Cao has a well-defined exact position after quotienting labels of
    equal-shaped pieces, because those relabelings fix Cao Cao. -/
def shapeCaoPosition (node : ShapeState) : Pos :=
  Quotient.liftOn node caoPosition (by
    intro source target sameShape
    exact sameShape.1)

@[simp] theorem shapeCaoPosition_ofState (state : ValidClassicState) :
    shapeCaoPosition (ShapeState.ofState state) = caoPosition state :=
  rfl

/-- Canonical Cao Cao position on the equal-shape graph. -/
def shapeCaoPositionOrbit (node : ShapeState) : Pos :=
  canonicalCaoPosition (shapeCaoPosition node)

/-- The canonical coordinate is invariant under the induced mirror
    automorphism of the equal-shape graph. -/
@[simp] theorem shapeCaoPositionOrbit_mirror (node : ShapeState) :
    shapeCaoPositionOrbit (mirrorShapeState node) =
      shapeCaoPositionOrbit node := by
  refine Quotient.inductionOn node ?_
  intro state
  exact caoPositionOrbit_mirror state

/-- The frontend's mirror-layer grouping key, defined directly on formal
    mirror-quotient nodes rather than on an arbitrary exported representative. -/
def mirrorCaoPositionOrbit (node : MirrorShapeState) : Pos :=
  Quotient.liftOn node shapeCaoPositionOrbit (by
    intro source target equivalent
    rcases equivalent with equal | mirrored
    · exact congrArg shapeCaoPositionOrbit equal
    · rw [← mirrored]
      exact (shapeCaoPositionOrbit_mirror source).symm)

@[simp] theorem mirrorCaoPositionOrbit_ofShapeState (node : ShapeState) :
    mirrorCaoPositionOrbit (MirrorShapeState.ofShapeState node) =
      shapeCaoPositionOrbit node :=
  rfl

@[simp] theorem mirrorCaoPositionOrbit_ofState
    (state : ValidClassicState) :
    mirrorCaoPositionOrbit (MirrorShapeState.ofState state) =
      caoPositionOrbit state :=
  rfl

end ClassicStateSpaceKernel
end Huarongdao
