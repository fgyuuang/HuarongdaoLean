import Huarongdao.Symmetry
import Huarongdao.StateSpace

namespace Huarongdao

/-- A classic state together with the proof that it is a legal board position. -/
abbrev ValidClassicState := { state : State // ValidState state }

/-- Equal-shaped pieces are observationally indistinguishable in the geometric puzzle. -/
def sameShapeSetoid : Setoid ValidClassicState where
  r := fun s t => SameShape s.1 t.1
  iseqv := {
    refl := fun s => sameShape_refl s.1
    symm := sameShape_symm
    trans := sameShape_trans
  }

/-- The quotient of legal labelled states by permutations of equal-shaped pieces. -/
abbrev ShapeState := Quotient sameShapeSetoid

/-- The classic puzzle restricted to legal states, ready for exact quotients. -/
def validClassicTask : StateSpace.Task ValidClassicState Action where
  initial := ⟨classic, classic_valid⟩
  goal := fun state => goal state.1 = true
  step := fun source action target =>
    tryMove source.1 action.piece action.direction = some target.1

/--
Forgetting the labels of equal-shaped pieces is already a well-defined
observation: in particular, goal status is constant on each shape class.
-/
def shapeObservation : StateSpace.Observation validClassicTask where
  setoid := sameShapeSetoid
  goal_iff := by
    intro source target sameShape
    change goal source.1 = true ↔ goal target.1 = true
    rw [sameShape_goal sameShape]

namespace ShapeState

def ofState (state : ValidClassicState) : ShapeState :=
  Quotient.mk sameShapeSetoid state

theorem ofState_eq {s t : ValidClassicState} (h : SameShape s.1 t.1) :
    ofState s = ofState t :=
  Quotient.sound h

theorem sameShape_of_ofState_eq {s t : ValidClassicState} (h : ofState s = ofState t) :
    SameShape s.1 t.1 :=
  Quotient.exact h

end ShapeState

/--
The relational image of `Step` on the quotient.  An edge exists when some legal
representatives have an exact one-step transition.  This is a sound abstraction;
full representative-wise bisimulation additionally requires move equivariance.
-/
def ShapeStep (source target : ShapeState) : Prop :=
  ∃ s t : ValidClassicState,
    ShapeState.ofState s = source ∧
    ShapeState.ofState t = target ∧
    Step s.1 t.1

/--
The existing quotient edge is exactly the generic relational-image edge.  The
generic theorem makes explicit that this is a sound abstraction before any
bisimulation proof is supplied.
-/
theorem shapeStep_iff_observationStep (source target : ShapeState) :
    ShapeStep source target ↔ shapeObservation.Step source target := by
  constructor
  · rintro ⟨s, t, source_eq, target_eq, ⟨action, executed⟩⟩
    exact ⟨s, action, t, source_eq, target_eq, executed⟩
  · rintro ⟨s, action, t, source_eq, target_eq, executed⟩
    exact ⟨s, t, source_eq, target_eq, ⟨action, executed⟩⟩

/--
The remaining representative-independence obligation for the equal-shape
quotient.  Proving this requires full equivariance of legal moves under
permutations of the four vertical blocks and the four soldiers.
-/
def SameShapeStepLift : Prop :=
  ∀ {source source' : ValidClassicState} {action : Action}
      {target : ValidClassicState},
    SameShape source.1 source'.1 →
    validClassicTask.step source action target →
    ∃ action' target',
      validClassicTask.step source' action' target' ∧
      SameShape target.1 target'.1

/-- Package a completed move-equivariance proof as an exact quotient. -/
def shapeBisimulation (step_lift : SameShapeStepLift) :
    StateSpace.BisimulationQuotient validClassicTask where
  toObservation := shapeObservation
  step_lift := step_lift

theorem shapeStep_of_step {s t : State} (hs : ValidState s) (ht : ValidState t)
    (h : Step s t) :
    ShapeStep (ShapeState.ofState ⟨s, hs⟩) (ShapeState.ofState ⟨t, ht⟩) :=
  ⟨⟨s, hs⟩, ⟨t, ht⟩, rfl, rfl, h⟩

/-- A quotient node is a goal when one (equivalently every) representative is a goal. -/
def ShapeGoal (node : ShapeState) : Prop :=
  ∃ state : ValidClassicState, ShapeState.ofState state = node ∧ goal state.1 = true

theorem shapeGoal_of_goal {state : ValidClassicState} (h : goal state.1 = true) :
    ShapeGoal (ShapeState.ofState state) :=
  ⟨state, rfl, h⟩

theorem shapeGoal_ofState_iff (state : ValidClassicState) :
    ShapeGoal (ShapeState.ofState state) ↔ goal state.1 = true := by
  constructor
  · rintro ⟨representative, equalClass, representativeGoal⟩
    have equivalent : SameShape representative.1 state.1 :=
      ShapeState.sameShape_of_ofState_eq equalClass
    rw [sameShape_goal equivalent] at representativeGoal
    exact representativeGoal
  · exact shapeGoal_of_goal

/-- Reflexive-transitive reachability in the relational image on equal-shape classes. -/
inductive ShapeReachable : ShapeState → ShapeState → Prop where
  | refl (node : ShapeState) : ShapeReachable node node
  | tail {source middle target : ShapeState} :
      ShapeStep source middle →
      ShapeReachable middle target →
      ShapeReachable source target

/-- Every concrete reachable path from a legal state projects to the quotient. -/
theorem reachable_to_shapeReachable {s t : State} (hs : ValidState s)
    (h : Reachable s t) :
    ShapeReachable
      (ShapeState.ofState ⟨s, hs⟩)
      (ShapeState.ofState ⟨t, reachable_preserves_validity hs h⟩) := by
  induction h with
  | refl => exact .refl _
  | tail step reachable ih =>
      have middleValid := step_preserves_validity hs step
      exact .tail (shapeStep_of_step hs middleValid step) (ih middleValid)

/-- Every proof-carrying executable path projects to the equal-shape quotient. -/
theorem Path.toShapeReachable (path : Path s t) (hs : ValidState s) :
    ShapeReachable
      (ShapeState.ofState ⟨s, hs⟩)
      (ShapeState.ofState ⟨t, path.target_valid hs⟩) := by
  simpa only using reachable_to_shapeReachable hs path.toReachable

end Huarongdao
