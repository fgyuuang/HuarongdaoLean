import Huarongdao.ClassicFullSpaceSoundness
import Huarongdao.ClassicFullSpaceCertificate
import Huarongdao.ClassicComponentSymmetryCertificate

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Semantic cardinality interface for the full shape space

`componentSummariesOf` is executable code.  The theorems in this file keep
the numerical native certificate separate from the semantic statement:
`ContinuousClass` is the quotient of *all* equal-shape states, whereas the
arrays are only a finite presentation of that quotient.  A
`ComponentRun.Lawful` proof is the bridge between these two levels.
-/

/-- The concrete DFS run used by the full-space analysis. -/
def fullSpaceRun : ComponentRun :=
  componentSummariesOf allShapeStates

/-- The run and the analysis use the same deterministic component summaries. -/
theorem fullSpaceRun_summaries :
    fullSpaceRun.summaries = analyze.summaries := by
  rfl

/-- A successful full-space run has exactly 898 roots.

This is a computation theorem about the executable run.  It is deliberately
separate from the semantic quotient theorem below.
-/
theorem fullSpaceRun_roots_size : fullSpaceRun.roots.size = 898 := by
  set_option maxHeartbeats 0 in
  native_decide

/-- The number of DFS roots agrees with the number of emitted summaries. -/
theorem fullSpaceRun_roots_eq_summaries :
    fullSpaceRun.roots.size = fullSpaceRun.summaries.size := by
  set_option maxHeartbeats 0 in
  native_decide

/-- The concrete finite run has the certified 898-component count. -/
theorem fullSpaceRun_component_count :
    fullSpaceRun.roots.size = 898 := fullSpaceRun_roots_size

/-- The concrete finite run covers the certified number of representatives. -/
theorem fullSpaceRun_state_count :
    allShapeStates.size = 65880 := by
  simpa [analyze, fullSpaceRun] using analysis_stateCount

/-- The first component containing the classical layout has the certified
    executable size. -/
theorem fullSpaceRun_classic_component_size :
    classicComponentSize = 25955 := by
  simpa [classicComponentSize, classicComponentIndex?, componentSummaries] using
    analysis_classicSize

/-!
### Conditional semantic theorem

The proposition below is the exact remaining proof boundary.  It asks for
the proof-facing obligations in `ComponentRun.Lawful`; no unchecked native
computation is hidden in the conclusion.
-/

theorem continuousClass_card_eq_898
    (lawful : fullSpaceRun.Lawful allShapeStates) :
    @Fintype.card ContinuousClass
      (VerifiedShapePartition.continuousClassFintype
        lawful.toVerifiedShapePartition) = 898 :=
  ComponentRun.Lawful.continuousClass_card_eq_898_of_lawful
    lawful fullSpaceRun_roots_size

/-!
### Component fibers and semantic class sizes

Counting array entries is not by itself a theorem about `ShapeState`: an
array could contain two labelled representatives of the same equal-shape
state.  The following equivalence therefore takes both semantic ingredients
explicitly:

* `VerifiedShapePartition` says that DFS labels are exactly reachability
  classes and that every `ShapeState` is represented;
* injectivity of `certificate.state` says that representatives are not
  duplicated in the quotient.
-/

def VerifiedShapePartition.IndexFiber
    (certificate : VerifiedShapePartition)
    (component : certificate.ComponentIndex) :=
  { index : certificate.StateIndex //
      certificate.classOf index = component }

def VerifiedShapePartition.SemanticFiber
    (certificate : VerifiedShapePartition)
    (component : certificate.ComponentIndex) :=
  { state : ShapeState //
      continuousClassOf state = certificate.rootClass component }

namespace VerifiedShapePartition

variable (certificate : VerifiedShapePartition)

def indexFiberToSemanticFiber
    (component : certificate.ComponentIndex) :
    certificate.IndexFiber component →
      certificate.SemanticFiber component :=
  fun index =>
    ⟨certificate.state index.1, by
      apply continuousClassOf_eq_iff.mpr
      apply certificate.reachable_of_component_eq
      exact index.2.trans (certificate.root_component component).symm⟩

theorem indexFiberToSemanticFiber_injective
    (stateInjective : Function.Injective certificate.state)
    (component : certificate.ComponentIndex) :
    Function.Injective (certificate.indexFiberToSemanticFiber component) := by
  intro left right equal
  apply Subtype.ext
  apply stateInjective
  exact congrArg Subtype.val equal

theorem indexFiberToSemanticFiber_surjective
    (component : certificate.ComponentIndex) :
    Function.Surjective (certificate.indexFiberToSemanticFiber component) := by
  intro target
  rcases certificate.complete target.1 with ⟨index, stateEq⟩
  have classEq :
      certificate.classOf index = component := by
    have quotientEq :
        continuousClassOf (certificate.state index) =
          continuousClassOf
            (certificate.state (certificate.root component)) := by
      simpa [rootClass, stateEq] using target.2
    exact
      (certificate.component_eq_of_reachable
        (continuousClassOf_eq_iff.mp quotientEq)).trans
          (certificate.root_component component)
  refine ⟨⟨index, classEq⟩, ?_⟩
  apply Subtype.ext
  exact stateEq

noncomputable def indexFiberEquivSemanticFiber
    (stateInjective : Function.Injective certificate.state)
    (component : certificate.ComponentIndex) :
    certificate.IndexFiber component ≃
      certificate.SemanticFiber component :=
  Equiv.ofBijective
    (certificate.indexFiberToSemanticFiber component)
    ⟨certificate.indexFiberToSemanticFiber_injective
        stateInjective component,
      certificate.indexFiberToSemanticFiber_surjective component⟩

noncomputable def semanticFiberFintype
    [Fintype certificate.IndexFiber component]
    (stateInjective : Function.Injective certificate.state) :
    Fintype (certificate.SemanticFiber component) :=
  Fintype.ofEquiv
    (certificate.IndexFiber component)
    (certificate.indexFiberEquivSemanticFiber stateInjective component)

theorem semanticFiber_card_eq
    [Fintype certificate.IndexFiber component]
    (stateInjective : Function.Injective certificate.state) :
    @Fintype.card (certificate.SemanticFiber component)
        (certificate.semanticFiberFintype stateInjective) =
      Fintype.card (certificate.IndexFiber component) := by
  letI : Fintype (certificate.SemanticFiber component) :=
    certificate.semanticFiberFintype stateInjective
  exact Fintype.card_congr
    (certificate.indexFiberEquivSemanticFiber stateInjective component).symm

end VerifiedShapePartition

/-!
### The computed classical component

The next three theorems are unconditional native computations.  They identify
component id `classicComponentId` inside the concrete DFS run and count its
index fiber.  No statement about the semantic quotient is made yet.
-/

theorem classicComponentId_lt_fullSpaceRun_roots :
    classicComponentId < fullSpaceRun.roots.size := by
  set_option maxHeartbeats 0 in
  native_decide

def fullSpaceClassicComponent : Fin fullSpaceRun.roots.size :=
  ⟨classicComponentId, classicComponentId_lt_fullSpaceRun_roots⟩

theorem fullSpaceClassicIndexFiber_card :
    Fintype.card
        { index : Fin allShapeStates.size //
          fullSpaceRun.componentOf.getD
              index.1 fullSpaceRun.roots.size =
            classicComponentId } =
      25955 := by
  set_option maxHeartbeats 0 in
  native_decide

def classicContinuousClassStates : Set ShapeState :=
  {state | continuousClassOf state = continuousClassOf classicShapeState}

def FullSpaceRepresentativesInjective
    (lawful : fullSpaceRun.Lawful allShapeStates) : Prop :=
  Function.Injective lawful.toVerifiedShapePartition.state

def FullSpaceClassicRootRepresents
    (lawful : fullSpaceRun.Lawful allShapeStates) : Prop :=
  lawful.toVerifiedShapePartition.rootClass fullSpaceClassicComponent =
    continuousClassOf classicShapeState

noncomputable def classicContinuousClassStatesFintype
    (lawful : fullSpaceRun.Lawful allShapeStates)
    (representativesInjective : FullSpaceRepresentativesInjective lawful)
    (classicRoot :
      FullSpaceClassicRootRepresents lawful) :
    Fintype { state : ShapeState //
      state ∈ classicContinuousClassStates } := by
  let certificate := lawful.toVerifiedShapePartition
  let computedFintype :
      Fintype (certificate.SemanticFiber fullSpaceClassicComponent) :=
    certificate.semanticFiberFintype representativesInjective
  let identify :
      certificate.SemanticFiber fullSpaceClassicComponent ≃
        { state : ShapeState // state ∈ classicContinuousClassStates } where
    toFun := fun state =>
      ⟨state.1, by
        change continuousClassOf state.1 =
          continuousClassOf classicShapeState
        exact state.2.trans classicRoot⟩
    invFun := fun state =>
      ⟨state.1, by
        change continuousClassOf state.1 =
          certificate.rootClass fullSpaceClassicComponent
        exact state.2.trans classicRoot.symm⟩
    left_inv := by
      intro state
      rfl
    right_inv := by
      intro state
      rfl
  exact @Fintype.ofEquiv
    (certificate.SemanticFiber fullSpaceClassicComponent)
    { state : ShapeState // state ∈ classicContinuousClassStates }
    computedFintype identify

theorem classicContinuousClass_card_eq_25955
    (lawful : fullSpaceRun.Lawful allShapeStates)
    (representativesInjective : FullSpaceRepresentativesInjective lawful)
    (classicRoot : FullSpaceClassicRootRepresents lawful) :
    @Fintype.card
        { state : ShapeState // state ∈ classicContinuousClassStates }
        (classicContinuousClassStatesFintype
          lawful representativesInjective classicRoot) =
      25955 := by
  let certificate := lawful.toVerifiedShapePartition
  let computedFintype :
      Fintype (certificate.SemanticFiber fullSpaceClassicComponent) :=
    certificate.semanticFiberFintype representativesInjective
  have semanticCount :
      @Fintype.card
          (certificate.SemanticFiber fullSpaceClassicComponent)
          computedFintype =
        25955 := by
    rw [certificate.semanticFiber_card_eq representativesInjective]
    exact fullSpaceClassicIndexFiber_card
  let identify :
      certificate.SemanticFiber fullSpaceClassicComponent ≃
        { state : ShapeState // state ∈ classicContinuousClassStates } where
    toFun := fun state =>
      ⟨state.1, state.2.trans classicRoot⟩
    invFun := fun state =>
      ⟨state.1, state.2.trans classicRoot.symm⟩
    left_inv := by intro state; rfl
    right_inv := by intro state; rfl
  exact (Fintype.card_congr identify.symm).trans semanticCount

end ClassicFullSpace
end Huarongdao
