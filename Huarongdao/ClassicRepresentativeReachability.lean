import Huarongdao.StateSpaceKernel
import Huarongdao.ClassicRepresentativeCertificate

namespace Huarongdao
namespace ClassicFullSpace

open ClassicRepresentativeCertificate

abbrev ContinuousEquivalent (source target : ShapeState) : Prop :=
  ClassicStateSpaceKernel.shape.Reachable source target

/--
The displayed DFS representative of component #15 is in the traditional
layout's continuous component. The expensive part is certified separately in
`ClassicRepresentativeCertificate`; this bridge performs no finite search.
-/
theorem classic_reaches_component_representative :
    ContinuousEquivalent
      (ShapeState.ofState ⟨classic, classic_valid⟩)
      classicComponentRepresentativeShapeState := by
  exact ⟨classicRepresentative_shapeWalk⟩

end ClassicFullSpace
end Huarongdao
