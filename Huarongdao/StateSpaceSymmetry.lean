import Huarongdao.MirrorQuotient

namespace Huarongdao
namespace StateSpace

universe u v w

/-!
This module isolates the group-action content behind exact symmetry quotients.
It deliberately uses a small self-contained group interface: the project does
not depend on Mathlib, so importing its hierarchy solely for quotients would
make the mathematical kernel substantially heavier.

The action is on the goal-labelled transition system.  It need not fix the
distinguished initial state pointwise: equal-shape relabelings, for example,
move the labelled classic initial state inside its orbit.  The quotient task
still has the orbit of the initial state as its distinguished root.
-/

/--
A group acting equivariantly on the states and action labels of a task.

`map_step` is stated in one direction.  Since every symmetry has an inverse,
`step_iff` below derives the converse rather than requiring duplicate data.
-/
structure SymmetryAction {State : Type u} {Action : Type v}
    (task : Task State Action) where
  Symmetry : Type w
  one : Symmetry
  mul : Symmetry → Symmetry → Symmetry
  inv : Symmetry → Symmetry
  mul_assoc : ∀ left middle right,
    mul (mul left middle) right = mul left (mul middle right)
  one_mul : ∀ symmetry, mul one symmetry = symmetry
  mul_one : ∀ symmetry, mul symmetry one = symmetry
  inv_mul : ∀ symmetry, mul (inv symmetry) symmetry = one
  mul_inv : ∀ symmetry, mul symmetry (inv symmetry) = one
  actState : Symmetry → State → State
  actAction : Symmetry → Action → Action
  actState_one : ∀ state, actState one state = state
  actState_mul : ∀ outer inner state,
    actState (mul outer inner) state =
      actState outer (actState inner state)
  actAction_one : ∀ action, actAction one action = action
  actAction_mul : ∀ outer inner action,
    actAction (mul outer inner) action =
      actAction outer (actAction inner action)
  goal_iff : ∀ symmetry state,
    task.goal (actState symmetry state) ↔ task.goal state
  map_step : ∀ symmetry {source action target},
    task.step source action target →
      task.step
        (actState symmetry source)
        (actAction symmetry action)
        (actState symmetry target)

namespace SymmetryAction

variable {State : Type u} {Action : Type v} {task : Task State Action}
variable (action : SymmetryAction.{u, v, w} task)

@[simp] theorem actState_inv (symmetry : action.Symmetry) (state : State) :
    action.actState (action.inv symmetry)
        (action.actState symmetry state) = state := by
  rw [← action.actState_mul, action.inv_mul, action.actState_one]

@[simp] theorem actState_inv_right
    (symmetry : action.Symmetry) (state : State) :
    action.actState symmetry
        (action.actState (action.inv symmetry) state) = state := by
  rw [← action.actState_mul, action.mul_inv, action.actState_one]

@[simp] theorem actAction_inv
    (symmetry : action.Symmetry) (label : Action) :
    action.actAction (action.inv symmetry)
        (action.actAction symmetry label) = label := by
  rw [← action.actAction_mul, action.inv_mul, action.actAction_one]

@[simp] theorem actAction_inv_right
    (symmetry : action.Symmetry) (label : Action) :
    action.actAction symmetry
        (action.actAction (action.inv symmetry) label) = label := by
  rw [← action.actAction_mul, action.mul_inv, action.actAction_one]

/-- A task step is present exactly when any group translate of it is present. -/
theorem step_iff (symmetry : action.Symmetry)
    {source : State} {label : Action} {target : State} :
    task.step
        (action.actState symmetry source)
        (action.actAction symmetry label)
        (action.actState symmetry target) ↔
      task.step source label target := by
  constructor
  · intro translated
    have restored := action.map_step (action.inv symmetry) translated
    simpa using restored
  · exact action.map_step symmetry

/-- Translate a proof-carrying walk by a symmetry. -/
def mapWalk (symmetry : action.Symmetry) :
    task.Walk source target →
      task.Walk
        (action.actState symmetry source)
        (action.actState symmetry target)
  | .nil _ => .nil _
  | .cons label first tail =>
      .cons (action.actAction symmetry label)
        (action.map_step symmetry first)
        (mapWalk symmetry tail)

@[simp] theorem mapWalk_length (symmetry : action.Symmetry)
    (walk : task.Walk source target) :
    (action.mapWalk symmetry walk).length = walk.length := by
  induction walk with
  | nil => rfl
  | cons label first tail ih =>
      simp [mapWalk, Task.Walk.length, ih]

/-- Reachability is invariant under every symmetry. -/
theorem reachable_iff (symmetry : action.Symmetry)
    (source target : State) :
    task.Reachable
        (action.actState symmetry source)
        (action.actState symmetry target) ↔
      task.Reachable source target := by
  constructor
  · rintro ⟨walk⟩
    exact ⟨by
      simpa using
        action.mapWalk (action.inv symmetry) walk⟩
  · rintro ⟨walk⟩
    exact ⟨action.mapWalk symmetry walk⟩

/-- Two states lie in the same orbit when one group element maps one to the other. -/
def OrbitEquiv (source target : State) : Prop :=
  ∃ symmetry : action.Symmetry,
    action.actState symmetry source = target

theorem orbit_refl (state : State) : action.OrbitEquiv state state :=
  ⟨action.one, action.actState_one state⟩

theorem orbit_symm {source target : State}
    (equivalent : action.OrbitEquiv source target) :
    action.OrbitEquiv target source := by
  rcases equivalent with ⟨symmetry, mapped⟩
  refine ⟨action.inv symmetry, ?_⟩
  rw [← mapped]
  exact action.actState_inv symmetry source

theorem orbit_trans {source middle target : State}
    (source_middle : action.OrbitEquiv source middle)
    (middle_target : action.OrbitEquiv middle target) :
    action.OrbitEquiv source target := by
  rcases source_middle with ⟨first, first_eq⟩
  rcases middle_target with ⟨second, second_eq⟩
  refine ⟨action.mul second first, ?_⟩
  calc
    action.actState (action.mul second first) source =
        action.actState second (action.actState first source) :=
      action.actState_mul second first source
    _ = action.actState second middle := by rw [first_eq]
    _ = target := second_eq

/-- The orbit equivalence relation induced by the group action. -/
def orbitSetoid : Setoid State where
  r := action.OrbitEquiv
  iseqv := {
    refl := action.orbit_refl
    symm := action.orbit_symm
    trans := action.orbit_trans
  }

/-- The observation that forgets the choice of representative inside an orbit. -/
def orbitObservation : Observation task where
  setoid := action.orbitSetoid
  goal_iff := by
    intro source target equivalent
    rcases equivalent with ⟨symmetry, mapped⟩
    rw [← mapped]
    exact (action.goal_iff symmetry source).symm

/--
Every group-action quotient is an exact bisimulation quotient.  The matching
step from a different representative is obtained by applying the witnessing
group element to both the action label and target.
-/
def orbitBisimulation : BisimulationQuotient task where
  toObservation := action.orbitObservation
  step_lift := by
    intro source source' label target equivalent step
    rcases equivalent with ⟨symmetry, source_eq⟩
    refine ⟨action.actAction symmetry label,
      action.actState symmetry target, ?_, ⟨symmetry, rfl⟩⟩
    rw [← source_eq]
    exact action.map_step symmetry step

/-- The task obtained by quotienting states by symmetry orbits. -/
def orbitTask : Task action.orbitObservation.Node Unit :=
  action.orbitObservation.quotientTask

/-- Every concrete step projects to an orbit-quotient step. -/
theorem orbitStep_of_step {source target : State} {label : Action}
    (step : task.step source label target) :
    action.orbitObservation.Step
      (action.orbitObservation.classOf source)
      (action.orbitObservation.classOf target) :=
  action.orbitObservation.step_of_step step

/--
Every quotient walk lifts from any representative of its source orbit,
preserving the number of primitive transitions.
-/
theorem liftOrbitWalkWithLength
    {sourceClass targetClass : action.orbitObservation.Node}
    (walk : action.orbitTask.Walk sourceClass targetClass)
    (source : State)
    (source_eq : action.orbitObservation.classOf source = sourceClass) :
    ∃ target, ∃ concreteWalk : task.Walk source target,
      concreteWalk.length = walk.length ∧
      action.orbitObservation.classOf target = targetClass :=
  action.orbitBisimulation.liftTaskWalkWithLength walk source source_eq

/-- Reachability in the orbit quotient is exactly liftable concrete reachability. -/
theorem orbitReachable_iff (source : State)
    (targetClass : action.orbitObservation.Node) :
    Observation.QuotientWalk.Reachable
        (observation := action.orbitObservation)
        (action.orbitObservation.classOf source)
        targetClass ↔
      ∃ target,
        task.Reachable source target ∧
        action.orbitObservation.classOf target = targetClass :=
  action.orbitBisimulation.quotientReachable_iff source targetClass

end SymmetryAction
end StateSpace

/-! ## The horizontal reflection as a two-element group action -/

/-- The two symmetries generated by horizontal reflection. -/
inductive HorizontalSymmetry where
  | identity
  | reflection
  deriving DecidableEq, Repr

namespace HorizontalSymmetry

def mul : HorizontalSymmetry → HorizontalSymmetry → HorizontalSymmetry
  | .identity, symmetry => symmetry
  | symmetry, .identity => symmetry
  | .reflection, .reflection => .identity

def inv (symmetry : HorizontalSymmetry) : HorizontalSymmetry :=
  symmetry

end HorizontalSymmetry

def horizontalActState :
    HorizontalSymmetry → ShapeState → ShapeState
  | .identity, state => state
  | .reflection, state => mirrorShapeState state

def horizontalActAction :
    HorizontalSymmetry → Unit → Unit :=
  fun _ _ => ()

/--
The maintained horizontal mirror is the orbit action of the two-element
reflection group on the equal-shape task.
-/
def horizontalMirrorAction :
    StateSpace.SymmetryAction shapeGraphTask where
  Symmetry := HorizontalSymmetry
  one := .identity
  mul := HorizontalSymmetry.mul
  inv := HorizontalSymmetry.inv
  mul_assoc := by
    intro left middle right
    cases left <;> cases middle <;> cases right <;> rfl
  one_mul := by intro symmetry; cases symmetry <;> rfl
  mul_one := by intro symmetry; cases symmetry <;> rfl
  inv_mul := by intro symmetry; cases symmetry <;> rfl
  mul_inv := by intro symmetry; cases symmetry <;> rfl
  actState := horizontalActState
  actAction := horizontalActAction
  actState_one := by intro state; rfl
  actState_mul := by
    intro outer inner state
    cases outer <;> cases inner <;>
      simp [HorizontalSymmetry.mul, horizontalActState]
  actAction_one := by intro action; cases action; rfl
  actAction_mul := by
    intro outer inner action
    cases action
    rfl
  goal_iff := by
    intro symmetry state
    cases symmetry with
    | identity => exact Iff.rfl
    | reflection => exact mirrorShape_goal_iff state
  map_step := by
    intro symmetry source label target step
    cases symmetry with
    | identity => exact step
    | reflection =>
        cases label
        apply (shapeStep_iff_observationStep _ _).mp
        exact shapeStep_mirror
          ((shapeStep_iff_observationStep _ _).mpr step)

/-- The generic orbit relation is exactly the maintained mirror relation. -/
theorem horizontalOrbitEquiv_iff_shapeMirrorEquiv
    (source target : ShapeState) :
    horizontalMirrorAction.OrbitEquiv source target ↔
      ShapeMirrorEquiv source target := by
  constructor
  · rintro ⟨symmetry, mapped⟩
    cases symmetry with
    | identity => exact Or.inl mapped
    | reflection => exact Or.inr mapped
  · intro equivalent
    rcases equivalent with equal | mirrored
    · exact ⟨.identity, equal⟩
    · exact ⟨.reflection, mirrored⟩

/-! ## Equal-shape relabelings as a second group action -/

namespace PieceRelabeling

/--
Two relabelings are equal when their forward permutations agree.  The inverse
is uniquely determined by the inverse laws; all remaining fields are proofs.
-/
theorem ext_forward {left right : PieceRelabeling}
    (equal : left.forward = right.forward) :
    left = right := by
  have inverseEqual : left.inverse = right.inverse := by
    funext piece
    calc
      left.inverse piece =
          left.inverse (right.forward (right.inverse piece)) := by
            rw [right.rightInv]
      _ = left.inverse (left.forward (right.inverse piece)) := by
            rw [equal]
      _ = right.inverse piece := left.leftInv _
  cases left
  cases right
  simp_all

theorem comp_assoc (left middle right : PieceRelabeling) :
    (left.comp middle).comp right = left.comp (middle.comp right) := by
  apply ext_forward
  funext piece
  rfl

theorem identity_comp (relabeling : PieceRelabeling) :
    identity.comp relabeling = relabeling := by
  apply ext_forward
  funext piece
  rfl

theorem comp_identity (relabeling : PieceRelabeling) :
    relabeling.comp identity = relabeling := by
  apply ext_forward
  funext piece
  rfl

theorem symm_comp (relabeling : PieceRelabeling) :
    relabeling.symm.comp relabeling = identity := by
  apply ext_forward
  funext piece
  exact relabeling.leftInv piece

theorem comp_symm (relabeling : PieceRelabeling) :
    relabeling.comp relabeling.symm = identity := by
  apply ext_forward
  funext piece
  exact relabeling.rightInv piece

end PieceRelabeling

/-- Relabel a valid state while retaining its validity proof. -/
def relabelValidState
    (relabeling : PieceRelabeling) (state : ValidClassicState) :
    ValidClassicState :=
  ⟨relabelState relabeling state.1, valid_relabel relabeling state.2⟩

/-- Relabel the moved piece while retaining the geometric direction. -/
def relabelAction (relabeling : PieceRelabeling) (action : Action) : Action :=
  ⟨relabeling.forward action.piece, action.direction⟩

/--
All shape-preserving permutations form a group action on the labelled valid
classic task.  Its orbit quotient is precisely the equal-shape quotient.
-/
def equalShapeRelabelingAction :
    StateSpace.SymmetryAction validClassicTask where
  Symmetry := PieceRelabeling
  one := PieceRelabeling.identity
  mul := PieceRelabeling.comp
  inv := PieceRelabeling.symm
  mul_assoc := PieceRelabeling.comp_assoc
  one_mul := PieceRelabeling.identity_comp
  mul_one := PieceRelabeling.comp_identity
  inv_mul := PieceRelabeling.symm_comp
  mul_inv := PieceRelabeling.comp_symm
  actState := relabelValidState
  actAction := relabelAction
  actState_one := by
    intro state
    apply Subtype.ext
    apply State.eq_of_valid_pos_eq
      (valid_relabel _ state.2) state.2
    intro piece
    simp [relabelState_pos, PieceRelabeling.identity]
  actState_mul := by
    intro outer inner state
    apply Subtype.ext
    exact (relabel_comp outer inner state.1).symm
  actAction_one := by
    intro action
    cases action
    rfl
  actAction_mul := by
    intro outer inner action
    cases action
    rfl
  goal_iff := by
    intro relabeling state
    change goal (relabelState relabeling state.1) = true ↔
      goal state.1 = true
    rw [goal_relabel]
  map_step := by
    intro relabeling source action target step
    exact tryMove_relabel_some relabeling step

/-- The orbit relation of relabelings is exactly geometric equal-shape equality. -/
theorem relabelingOrbitEquiv_iff_sameShape
    (source target : ValidClassicState) :
    equalShapeRelabelingAction.OrbitEquiv source target ↔
      SameShape source.1 target.1 := by
  constructor
  · rintro ⟨relabeling, mapped⟩
    have same :
        SameShape (relabelState relabeling source.1) source.1 :=
      relabel_sameShape relabeling source.1
    rw [show relabelState relabeling source.1 = target.1 from
      congrArg Subtype.val mapped] at same
    exact sameShape_symm same
  · intro same
    let relabeling :=
      sameShapeRelabeling source.2 target.2 same
    refine ⟨relabeling, ?_⟩
    apply Subtype.ext
    exact sameShapeRelabeling_eq source.2 target.2 same

end Huarongdao
