import Huarongdao.StateSpaceSymmetry
import Huarongdao.MirrorSearch
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.GroupAction.Quotient

namespace Huarongdao
namespace StateSpace
namespace SymmetryAction

universe u v w

variable {State : Type u} {Action : Type v} {task : Task State Action}

/--
The mathlib orbit setoid induced by the operations stored in the project's
self-contained symmetry action.

This adapter keeps the existing labelled transition-system API intact while
making mathlib's orbit, quotient, stabilizer, and counting results available.
-/
def mathlibOrbitRel
    (action : SymmetryAction.{u, v, w} task) : Setoid State := by
  letI : Mul action.Symmetry := ⟨action.mul⟩
  letI : One action.Symmetry := ⟨action.one⟩
  letI : Inv action.Symmetry := ⟨action.inv⟩
  letI : Group action.Symmetry :=
    Group.ofLeftAxioms action.mul_assoc action.one_mul action.inv_mul
  letI : SMul action.Symmetry State := ⟨action.actState⟩
  letI : MulAction action.Symmetry State := {
    one_smul := action.actState_one
    mul_smul := action.actState_mul
  }
  exact MulAction.orbitRel action.Symmetry State

/--
The project's orbit relation is extensionally the orbit relation built by
mathlib from the same group action.
-/
theorem orbitEquiv_iff_mathlibOrbitRel
    (action : SymmetryAction.{u, v, w} task)
    (source target : State) :
    action.OrbitEquiv source target ↔
      action.mathlibOrbitRel source target := by
  change
    (∃ symmetry, action.actState symmetry source = target) ↔
      ∃ symmetry, action.actState symmetry target = source
  constructor
  · rintro ⟨symmetry, mapped⟩
    refine ⟨action.inv symmetry, ?_⟩
    rw [← mapped]
    exact action.actState_inv symmetry source
  · rintro ⟨symmetry, mapped⟩
    refine ⟨action.inv symmetry, ?_⟩
    rw [← mapped]
    exact action.actState_inv symmetry target

/-- The project's orbit quotient and mathlib's orbit quotient are equivalent. -/
def orbitQuotientEquivMathlib
    (action : SymmetryAction.{u, v, w} task) :
    Quotient action.orbitSetoid ≃
      Quotient action.mathlibOrbitRel :=
  Quotient.congrRight (action.orbitEquiv_iff_mathlibOrbitRel)

end SymmetryAction
end StateSpace

/-! ## Concrete mathlib group actions -/

instance horizontalSymmetryGroup : Group HorizontalSymmetry where
  mul := HorizontalSymmetry.mul
  one := .identity
  inv := HorizontalSymmetry.inv
  mul_assoc := by
    intro left middle right
    cases left <;> cases middle <;> cases right <;> rfl
  one_mul := by intro symmetry; cases symmetry <;> rfl
  mul_one := by intro symmetry; cases symmetry <;> rfl
  inv_mul_cancel := by intro symmetry; cases symmetry <;> rfl

instance horizontalSymmetryFintype : Fintype HorizontalSymmetry where
  elems := {.identity, .reflection}
  complete := by intro symmetry; cases symmetry <;> simp

theorem horizontalSymmetry_card :
    Fintype.card HorizontalSymmetry = 2 := by
  decide

instance horizontalSymmetryShapeAction :
    MulAction HorizontalSymmetry ShapeState where
  smul := horizontalActState
  one_smul := horizontalMirrorAction.actState_one
  mul_smul := horizontalMirrorAction.actState_mul

instance horizontalSymmetryLabelAction :
    MulAction HorizontalSymmetry Unit where
  smul := horizontalActAction
  one_smul := horizontalMirrorAction.actAction_one
  mul_smul := horizontalMirrorAction.actAction_mul

noncomputable instance horizontalOrbitFintype (state : ShapeState) :
    Fintype (MulAction.orbit HorizontalSymmetry state) :=
  (Finite.finite_mulAction_orbit state).fintype

instance horizontalStabilizerFinite (state : ShapeState) :
    Finite (MulAction.stabilizer HorizontalSymmetry state) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance horizontalStabilizerFintype (state : ShapeState) :
    Fintype (MulAction.stabilizer HorizontalSymmetry state) :=
  Fintype.ofFinite _

instance pieceRelabelingGroup : Group PieceRelabeling where
  mul := PieceRelabeling.comp
  one := PieceRelabeling.identity
  inv := PieceRelabeling.symm
  mul_assoc := PieceRelabeling.comp_assoc
  one_mul := PieceRelabeling.identity_comp
  mul_one := PieceRelabeling.comp_identity
  inv_mul_cancel := PieceRelabeling.symm_comp

instance pieceRelabelingStateAction :
    MulAction PieceRelabeling ValidClassicState where
  smul := relabelValidState
  one_smul := equalShapeRelabelingAction.actState_one
  mul_smul := equalShapeRelabelingAction.actState_mul

instance pieceRelabelingLabelAction :
    MulAction PieceRelabeling Action where
  smul := relabelAction
  one_smul := equalShapeRelabelingAction.actAction_one
  mul_smul := equalShapeRelabelingAction.actAction_mul

/-- The maintained reflection orbit relation is mathlib's orbit relation. -/
theorem horizontalOrbitEquiv_iff_mathlibOrbitRel
    (source target : ShapeState) :
    horizontalMirrorAction.OrbitEquiv source target ↔
      MulAction.orbitRel HorizontalSymmetry ShapeState source target := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm,
    MulAction.mem_orbit_iff]
  rfl

/-- Equal-shape relabeling orbits are mathlib orbits. -/
theorem relabelingOrbitEquiv_iff_mathlibOrbitRel
    (source target : ValidClassicState) :
    equalShapeRelabelingAction.OrbitEquiv source target ↔
      MulAction.orbitRel PieceRelabeling ValidClassicState source target := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm,
    MulAction.mem_orbit_iff]
  rfl

/-- The mathlib orbit space for horizontal reflection on equal-shape states. -/
abbrev HorizontalOrbitSpace :=
  MulAction.orbitRel.Quotient HorizontalSymmetry ShapeState

/-- The mathlib orbit space for equal-shape relabelings. -/
abbrev RelabelingOrbitSpace :=
  MulAction.orbitRel.Quotient PieceRelabeling ValidClassicState

/-- The maintained mirror quotient is exactly the mathlib reflection orbit space. -/
def mirrorShapeStateEquivMathlibOrbit :
    MirrorShapeState ≃ HorizontalOrbitSpace :=
  Quotient.congrRight (by
    intro source target
    change ShapeMirrorEquiv source target ↔
      MulAction.orbitRel HorizontalSymmetry ShapeState source target
    rw [← horizontalOrbitEquiv_iff_mathlibOrbitRel,
      horizontalOrbitEquiv_iff_shapeMirrorEquiv])

/-- The maintained equal-shape quotient is exactly the relabeling orbit space. -/
def shapeStateEquivMathlibOrbit :
    ShapeState ≃ RelabelingOrbitSpace :=
  Quotient.congrRight (by
    intro source target
    change SameShape source.1 target.1 ↔
      MulAction.orbitRel PieceRelabeling ValidClassicState source target
    rw [← relabelingOrbitEquiv_iff_mathlibOrbitRel,
      relabelingOrbitEquiv_iff_sameShape])

/-- The subgroup of horizontal symmetries fixing an equal-shape state. -/
def horizontalStabilizer (state : ShapeState) : Subgroup HorizontalSymmetry :=
  MulAction.stabilizer HorizontalSymmetry state

/-- Reflection fixes a state exactly when it belongs to that state's stabilizer. -/
theorem reflection_mem_horizontalStabilizer_iff
    (state : ShapeState) :
    HorizontalSymmetry.reflection ∈ horizontalStabilizer state ↔
      mirrorShapeState state = state := by
  rw [horizontalStabilizer, MulAction.mem_stabilizer_iff]
  rfl

/-- Orbit-stabilizer specialized to the two-element reflection group. -/
theorem horizontal_orbit_mul_stabilizer_card
    (state : ShapeState) :
    Fintype.card (MulAction.orbit HorizontalSymmetry state) *
        Fintype.card (MulAction.stabilizer HorizontalSymmetry state) = 2 := by
  calc
    _ = Fintype.card HorizontalSymmetry :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        HorizontalSymmetry state
    _ = 2 := horizontalSymmetry_card

/-- A shape state is globally fixed exactly when reflection fixes it. -/
theorem mem_horizontalFixedPoints_iff
    (state : ShapeState) :
    state ∈ MulAction.fixedPoints HorizontalSymmetry ShapeState ↔
      mirrorShapeState state = state := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro fixed
    exact fixed .reflection
  · intro reflected symmetry
    cases symmetry with
    | identity => rfl
    | reflection => exact reflected

/-- Horizontally symmetric states have singleton reflection orbits. -/
theorem horizontalOrbit_card_eq_one_iff
    (state : ShapeState) :
    Fintype.card (MulAction.orbit HorizontalSymmetry state) = 1 ↔
      mirrorShapeState state = state := by
  rw [← mem_horizontalFixedPoints_iff,
    MulAction.mem_fixedPoints_iff_card_orbit_eq_one]

/-- Non-symmetric states occur in two-element reflection orbits. -/
theorem horizontalOrbit_card_eq_two_iff
    (state : ShapeState) :
    Fintype.card (MulAction.orbit HorizontalSymmetry state) = 2 ↔
      mirrorShapeState state ≠ state := by
  constructor
  · intro cardTwo fixed
    have cardOne := (horizontalOrbit_card_eq_one_iff state).2 fixed
    omega
  · intro notFixed
    have positive :
        0 < Fintype.card (MulAction.orbit HorizontalSymmetry state) :=
      Fintype.card_pos_iff.mpr
        ⟨⟨state, MulAction.mem_orbit_self state⟩⟩
    have bounded :
        Fintype.card (MulAction.orbit HorizontalSymmetry state) ≤ 2 := by
      calc
        _ ≤ Fintype.card HorizontalSymmetry :=
          Fintype.card_le_of_surjective
            (fun symmetry : HorizontalSymmetry =>
              ⟨symmetry • state, MulAction.mem_orbit state symmetry⟩)
            (by
              rintro ⟨target, symmetry, rfl⟩
              exact ⟨symmetry, rfl⟩)
        _ = 2 := horizontalSymmetry_card
    have notOne :
        Fintype.card (MulAction.orbit HorizontalSymmetry state) ≠ 1 := by
      intro cardOne
      exact notFixed ((horizontalOrbit_card_eq_one_iff state).1 cardOne)
    omega

/-! ## Executable and semantic mirror quotient bridge -/

/--
The executable raw-state mirror equivalence is exactly equality in the
maintained semantic two-stage quotient.
-/
theorem mirrorRepresentativeEq_iff_mirrorShapeState_ofState_eq
    {source target : State}
    (sourceValid : ValidState source)
    (targetValid : ValidState target) :
    MirrorRepresentativeEq source target ↔
      MirrorShapeState.ofState ⟨source, sourceValid⟩ =
        MirrorShapeState.ofState ⟨target, targetValid⟩ := by
  constructor
  · intro equivalent
    apply Quotient.sound
    rcases equivalent with same | mirrored
    · exact Or.inl (ShapeState.ofState_eq same)
    · exact Or.inr (by
        simpa using
          ShapeState.ofState_eq
            (s := mirrorValidState ⟨source, sourceValid⟩)
            (t := ⟨target, targetValid⟩)
            mirrored)
  · intro equalClass
    have equivalent :
        ShapeMirrorEquiv
          (ShapeState.ofState ⟨source, sourceValid⟩)
          (ShapeState.ofState ⟨target, targetValid⟩) :=
      Quotient.exact equalClass
    rcases equivalent with same | mirrored
    · exact Or.inl (ShapeState.sameShape_of_ofState_eq same)
    · exact Or.inr
        (ShapeState.sameShape_of_ofState_eq (by
          simpa using mirrored))

/-- The executable mirror relation restricted to valid classic states. -/
def mirrorRepresentativeSetoid : Setoid ValidClassicState where
  r := fun source target =>
    MirrorRepresentativeEq source.1 target.1
  iseqv := {
    refl := fun state => mirrorRepresentativeEq_refl state.1
    symm := fun {source target} equivalent =>
      mirrorRepresentativeEq_symm
        source.2 target.2 equivalent
    trans := fun {source middle target} first second =>
      mirrorRepresentativeEq_trans
        source.2 middle.2 target.2 first second
  }

/-- Map an executable mirror class into the semantic mirror quotient. -/
def executableMirrorClassToSemantic :
    Quotient mirrorRepresentativeSetoid → MirrorShapeState :=
  Quotient.lift MirrorShapeState.ofState (by
    intro source target equivalent
    exact
      (mirrorRepresentativeEq_iff_mirrorShapeState_ofState_eq
        source.2 target.2).mp equivalent)

theorem executableMirrorClassToSemantic_bijective :
    Function.Bijective executableMirrorClassToSemantic := by
  constructor
  · intro sourceClass targetClass equal
    induction sourceClass using Quotient.inductionOn with
    | _ source =>
        induction targetClass using Quotient.inductionOn with
        | _ target =>
            apply Quotient.sound
            exact
              (mirrorRepresentativeEq_iff_mirrorShapeState_ofState_eq
                source.2 target.2).mpr equal
  · intro targetClass
    induction targetClass using Quotient.inductionOn with
    | _ shapeState =>
        induction shapeState using Quotient.inductionOn with
        | _ state =>
            exact ⟨Quotient.mk mirrorRepresentativeSetoid state, rfl⟩

/--
The quotient of valid raw states by the executable relation is equivalent to
the maintained semantic two-stage quotient.
-/
noncomputable def executableMirrorQuotientEquivSemantic :
    Quotient mirrorRepresentativeSetoid ≃ MirrorShapeState :=
  Equiv.ofBijective executableMirrorClassToSemantic
    executableMirrorClassToSemantic_bijective

end Huarongdao
