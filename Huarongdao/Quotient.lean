import Huarongdao.Relabeling
import Huarongdao.StateSpace
import Huarongdao.Reversibility

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

/-- Representative-wise step lifting for the equal-shape quotient. -/
def SameShapeStepLift : Prop :=
  ∀ {source source' : ValidClassicState} {action : Action}
      {target : ValidClassicState},
    SameShape source.1 source'.1 →
    validClassicTask.step source action target →
    ∃ action' target',
      validClassicTask.step source' action' target' ∧
      SameShape target.1 target'.1

/--
Every legal move from one representative can be matched from every
equal-shape representative by transporting it along the induced relabeling.
-/
theorem sameShapeStepLift : SameShapeStepLift := by
  intro source source' action target equivalent executed
  let relabeling :=
    sameShapeRelabeling source.2 source'.2 equivalent
  have source_eq :
      relabelState relabeling source.1 = source'.1 :=
    sameShapeRelabeling_eq source.2 source'.2 equivalent
  have relabelledMove :=
    tryMove_relabel_some relabeling executed
  rw [source_eq] at relabelledMove
  let action' : Action :=
    ⟨relabeling.forward action.piece, action.direction⟩
  let target' : ValidClassicState :=
    ⟨relabelState relabeling target.1, valid_relabel relabeling target.2⟩
  refine ⟨action', target', ?_, ?_⟩
  · exact relabelledMove
  · exact sameShape_symm (relabel_sameShape relabeling target.1)

/-- Every equal-shape quotient edge between valid states is reversible:
    the reverse primitive move is transported back through the equal-shape
    class of the target. -/
theorem qstep_symm_of_valid {s t : State}
    (hs : ValidState s) (ht : ValidState t) (h : QStep s t) :
    QStep t s := by
  rcases h with ⟨p, d, next, executed, equivalent⟩
  have nextValid := tryMove_preserves_validity executed
  have lift := sameShapeStepLift
    (source := ⟨next, nextValid⟩)
    (source' := ⟨t, ht⟩)
    (action := ⟨p, d.reverse⟩)
    (target := ⟨s, hs⟩)
    equivalent
    (tryMove_reverse hs executed)
  rcases lift with ⟨action', target', step', shape⟩
  exact ⟨action'.piece, action'.direction, target'.1, step', sameShape_symm shape⟩

/-- The equal-shape observation is an exact bisimulation quotient. -/
def shapeBisimulation :
    StateSpace.BisimulationQuotient validClassicTask where
  toObservation := shapeObservation
  step_lift := sameShapeStepLift

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
