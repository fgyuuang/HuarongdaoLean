import Huarongdao.ClassicContinuousClassCardCore

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Unconditional cardinality export

The expensive finite replay is isolated in
`ClassicFullSpaceFiniteCertificate`.  Everything below is proof-only and
reuses that certificate together with the semantic enumeration certificate.
-/

theorem fullSpaceRun_lawful :
    fullSpaceRun.Lawful allShapeStates :=
  fullSpaceRun_lawful_core

theorem continuousClass_card_eq_898_complete :
    @Fintype.card ContinuousClass
      (ComponentRun.Lawful.continuousClassFintypeOfLawful
        fullSpaceRun_lawful) = 898 :=
  continuousClass_card_eq_898_complete_core

end ClassicFullSpace
end Huarongdao
