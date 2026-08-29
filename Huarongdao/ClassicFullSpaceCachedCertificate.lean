import Huarongdao.ClassicFullSpaceCertificate
import Huarongdao.ClassicComponentSymmetry

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Shared full-space certificate interface

This module is deliberately non-computational.  `ClassicFullSpaceCertificate`
is the single module that performs the expensive native check.  Downstream
modules should import this interface and consume these projections instead of
introducing another `native_decide` over `allShapeStates`.
-/

structure FullSpaceCachedFacts : Prop where
  stateCount : analyze.stateCount = 65880
  allValid : analyze.allValid = true
  keysUnique : analyze.keysUnique = true
  closed : analyze.closed = true
  componentCount : analyze.summaries.size = 898
  coveredCount : analyze.coveredCount = 65880
  classicSize : analyze.classicSize = 25955

/-- The one shared proof object exported by the full-space certificate. -/
theorem fullSpace_cached_facts : FullSpaceCachedFacts :=
  {
    stateCount := analysis_stateCount
    allValid := analysis_allValid
    keysUnique := analysis_keysUnique
    closed := analysis_closed
    componentCount := analysis_componentCount
    coveredCount := analysis_coveredCount
    classicSize := analysis_classicSize
  }

theorem cached_stateCount : analyze.stateCount = 65880 :=
  fullSpace_cached_facts.stateCount

theorem cached_allValid : analyze.allValid = true :=
  fullSpace_cached_facts.allValid

theorem cached_keysUnique : analyze.keysUnique = true :=
  fullSpace_cached_facts.keysUnique

theorem cached_closed : analyze.closed = true :=
  fullSpace_cached_facts.closed

theorem cached_componentCount : analyze.summaries.size = 898 :=
  fullSpace_cached_facts.componentCount

theorem cached_coveredCount : analyze.coveredCount = 65880 :=
  fullSpace_cached_facts.coveredCount

theorem cached_classicSize : analyze.classicSize = 25955 :=
  fullSpace_cached_facts.classicSize

/-!
The following facts all inspect the same executable DFS run.  Keeping them in
one proposition gives `native_decide` one certificate boundary; downstream
theorems only project these fields and do not independently traverse the
65,880-state array.
-/
structure FullSpaceRunCachedFacts : Prop where
  rootsSize : fullSpaceRun.roots.size = 898
  classicIdBound : classicComponentId < fullSpaceRun.roots.size
  classicFiberCard :
    Fintype.card
        { index : Fin allShapeStates.size //
          fullSpaceRun.componentOf.getD
              index.1 fullSpaceRun.roots.size =
            classicComponentId } =
      25955

def fullSpaceRunCachedClaims : Prop :=
  fullSpaceRun.roots.size = 898 ∧
  classicComponentId < fullSpaceRun.roots.size ∧
  Fintype.card
      { index : Fin allShapeStates.size //
        fullSpaceRun.componentOf.getD
            index.1 fullSpaceRun.roots.size =
          classicComponentId } =
    25955

instance fullSpaceRunCachedClaimsDecidable :
    Decidable fullSpaceRunCachedClaims := by
  unfold fullSpaceRunCachedClaims
  infer_instance

theorem fullSpace_run_cached_facts : FullSpaceRunCachedFacts := by
  set_option maxHeartbeats 0 in
  have checked : fullSpaceRunCachedClaims := by
    native_decide
  rcases checked with ⟨rootsSize, classicIdBound, classicFiberCard⟩
  exact {
    rootsSize := rootsSize
    classicIdBound := classicIdBound
    classicFiberCard := classicFiberCard
  }

theorem cached_fullSpaceRun_roots_size :
    fullSpaceRun.roots.size = 898 :=
  fullSpace_run_cached_facts.rootsSize

theorem cached_classicComponentId_lt_fullSpaceRun_roots :
    classicComponentId < fullSpaceRun.roots.size :=
  fullSpace_run_cached_facts.classicIdBound

theorem cached_fullSpaceClassicIndexFiber_card :
    Fintype.card
        { index : Fin allShapeStates.size //
          fullSpaceRun.componentOf.getD
              index.1 fullSpaceRun.roots.size =
            classicComponentId } =
      25955 :=
  fullSpace_run_cached_facts.classicFiberCard

end ClassicFullSpace
end Huarongdao
