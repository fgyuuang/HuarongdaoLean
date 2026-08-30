import Huarongdao.ClassicFullSpaceSoundness
import Huarongdao.ClassicFullSpaceCertificate
import Huarongdao.ClassicFullSpaceFiniteCertificate
import Huarongdao.ClassicFullSpaceRootCountCertificate
import Huarongdao.ClassicFullSpaceUnique
import Huarongdao.ClassicFullSpaceCompleteness

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Proof-only core for the unconditional component-cardinality theorem

This file deliberately avoids `ClassicFullSpaceCachedCertificate`: that legacy
interface also computes the classical component fibre.  The theorem below
needs only the finite replay certificate, the generator completeness theorem,
the indexed-state uniqueness theorem, and the cached root count.
-/

private theorem core_all_valid :
    ∀ index : Fin allShapeStates.size, ValidState allShapeStates[index] := by
  intro index
  exact ComponentRun.Lawful.checkAllValid_sound
    (by
      simpa [analyze, ComponentRun.Lawful.checkAllValid] using
        analysis_allValid)
    index.2

theorem fullSpace_semantic_complete_core :
    ∀ node : ShapeState,
      ∃ index : Fin allShapeStates.size,
        ShapeState.ofState
            ⟨allShapeStates[index], core_all_valid index⟩ =
          node := by
  exact enumerationComplete_quotient_cover
    core_all_valid
    enumerationComplete

private theorem fullSpace_array_member_core
    (index : Fin allShapeStates.size) :
    allShapeStates[index] ∈ allShapeStatesList := by
  have member :
      allShapeStates[index] ∈ allShapeStates.toList :=
    Array.getElem_mem_toList index.2
  simpa [allShapeStates] using member

private theorem fullSpace_shape_exact_core
    (stateInjective :
      Function.Injective
        (fun index : Fin allShapeStates.size => allShapeStates[index]))
    (validAt : ∀ index : Fin allShapeStates.size,
      ValidState allShapeStates[index])
    {left right : Fin allShapeStates.size}
    (sameState :
      ShapeState.ofState ⟨allShapeStates[left], validAt left⟩ =
        ShapeState.ofState ⟨allShapeStates[right], validAt right⟩) :
    fullSpaceRun.componentOf.getD left.1 fullSpaceRun.roots.size =
      fullSpaceRun.componentOf.getD right.1 fullSpaceRun.roots.size := by
  have sameShape :
      SameShape allShapeStates[left] allShapeStates[right] :=
    ShapeState.sameShape_of_ofState_eq sameState
  have stateEq : allShapeStates[left] = allShapeStates[right] :=
    generated_sameShape_eq
      (validAt left) (validAt right)
      (fullSpace_array_member_core left)
      (fullSpace_array_member_core right)
      sameShape
  have indexEq : left = right := by
    apply stateInjective
    exact stateEq
  cases indexEq
  rfl

theorem fullSpace_semanticCertificate_core
    (stateInjective :
      Function.Injective
        (fun index : Fin allShapeStates.size => allShapeStates[index])) :
    ComponentRun.Lawful.SemanticCertificate
      allShapeStates fullSpaceRun := by
  let validAt : ∀ index : Fin allShapeStates.size,
      ValidState allShapeStates[index] := core_all_valid
  refine {
    complete := ?_
    shape_exact := ?_
  }
  · intro _ node
    exact fullSpace_semantic_complete_core node
  · intro validAt' left right sameState
    exact fullSpace_shape_exact_core
      stateInjective validAt' sameState

theorem fullSpace_stateInjective_core :
    Function.Injective
      (fun index : Fin allShapeStates.size => allShapeStates[index]) :=
  allShapeStates_state_injective

theorem fullSpaceRun_lawful_core :
    fullSpaceRun.Lawful allShapeStates :=
  ComponentRun.Lawful.lawful_of_checked
    fullSpaceRun_checkFinite_checked
    (fullSpace_semanticCertificate_core fullSpace_stateInjective_core)

theorem continuousClass_card_eq_898_complete_core :
    @Fintype.card ContinuousClass
      (ComponentRun.Lawful.continuousClassFintypeOfLawful
        fullSpaceRun_lawful_core) = 898 :=
  ComponentRun.Lawful.continuousClass_card_eq_898_of_lawful
    fullSpaceRun_lawful_core
    fullSpaceRun_roots_size_checked

end ClassicFullSpace
end Huarongdao
