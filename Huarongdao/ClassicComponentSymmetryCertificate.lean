import Huarongdao.ClassicComponentSymmetry

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/-- Native certification of the reflection actions on all 898 components. -/
theorem componentSymmetries_checked :
    checkComponentSymmetries = true := by
  set_option maxHeartbeats 0 in
  native_decide

theorem componentSymmetry_facts : componentSymmetryClaims :=
  of_decide_eq_true componentSymmetries_checked

private structure CertifiedComponentSymmetryFacts : Prop where
  horizontalOrbitCount :
    componentOrbitCount horizontalComponentMap = 459
  horizontalFixedCount :
    fixedComponentCount horizontalComponentMap = 20
  componentIdsDistinct :
    classicComponentId ≠ verticalClassicComponentId
  classicSize :
    componentSize classicComponentId = 25955
  verticalClassicSize :
    componentSize verticalClassicComponentId = 25955
  verticalForward :
    verticalComponentMap.getD classicComponentId 898 =
      verticalClassicComponentId
  verticalBackward :
    verticalComponentMap.getD verticalClassicComponentId 898 =
      classicComponentId

private theorem certifiedComponentSymmetryFacts :
    CertifiedComponentSymmetryFacts := by
  set_option maxHeartbeats 0 in
    have facts := componentSymmetry_facts
    unfold componentSymmetryClaims at facts
    rcases facts with
      ⟨_, _, _, _, _, horizontalFixed, horizontalOrbits, idsDistinct,
        classicSize, verticalClassicSize, verticalForward, verticalBackward⟩
    exact {
      horizontalOrbitCount := by
        simpa [horizontalComponentMap] using horizontalOrbits
      horizontalFixedCount := by
        simpa [horizontalComponentMap] using horizontalFixed
      componentIdsDistinct := by
        simpa [classicComponentId, verticalClassicComponentId] using idsDistinct
      classicSize := by
        simpa [componentSize, componentLabeling, classicComponentId] using
          classicSize
      verticalClassicSize := by
        simpa [componentSize, componentLabeling,
          verticalClassicComponentId] using verticalClassicSize
      verticalForward := by
        simpa [verticalComponentMap, classicComponentId,
          verticalClassicComponentId] using verticalForward
      verticalBackward := by
        simpa [verticalComponentMap, classicComponentId,
          verticalClassicComponentId] using verticalBackward
    }

/-- Horizontal reflection has exactly 459 orbits on the computed components. -/
theorem horizontalComponentOrbitCount_eq :
    componentOrbitCount horizontalComponentMap = 459 :=
  certifiedComponentSymmetryFacts.horizontalOrbitCount

/-- Exactly twenty computed components are fixed by horizontal reflection. -/
theorem horizontalFixedComponentCount_eq :
    fixedComponentCount horizontalComponentMap = 20 :=
  certifiedComponentSymmetryFacts.horizontalFixedCount

/-- The traditional layout and its vertical reflection have different ids. -/
theorem classicComponentId_ne_verticalClassicComponentId :
    classicComponentId ≠ verticalClassicComponentId :=
  certifiedComponentSymmetryFacts.componentIdsDistinct

/-- Both components exchanged by vertical reflection contain 25,955 states. -/
theorem verticalReflection_largeComponentSizes :
    componentSize classicComponentId = 25955 ∧
      componentSize verticalClassicComponentId = 25955 :=
  ⟨certifiedComponentSymmetryFacts.classicSize,
    certifiedComponentSymmetryFacts.verticalClassicSize⟩

/-- Vertical reflection exchanges the two 25,955-state components. -/
theorem verticalReflection_exchanges_largeComponents :
    verticalComponentMap.getD classicComponentId 898 =
        verticalClassicComponentId ∧
      verticalComponentMap.getD verticalClassicComponentId 898 =
        classicComponentId :=
  ⟨certifiedComponentSymmetryFacts.verticalForward,
    certifiedComponentSymmetryFacts.verticalBackward⟩

/-- The vertical reflection is absent from the closed classic component. -/
theorem verticalClassicSeparated_checked :
    checkVerticalClassicSeparated = true := by
  set_option maxHeartbeats 0 in
  native_decide

/-- The traditional state cannot reach its vertical reflection by legal slides. -/
theorem not_continuousEquivalent_classic_verticalMirror :
    ¬ContinuousEquivalent classicShapeState verticalClassicShapeState :=
  not_continuousEquivalent_classic_verticalMirror_of_check
    verticalClassicSeparated_checked

end ClassicFullSpace
end Huarongdao
