import Huarongdao.ClassicSolution
import Huarongdao.Search
import Std.Tactic

namespace Huarongdao

/-- The complete equal-shape quotient graph rooted at the classic layout. -/
def classicQuotientGraph : Graph := enumerate classic

/-- Native evaluation checks the large graph; this theorem is then consumed by
    the generic soundness proof in `Search.lean`. -/
theorem classicQuotientLowerBound_checked :
    checkQuotientLowerBound classicQuotientGraph classic 116 = true := by
  set_option maxHeartbeats 0 in
  native_decide

/-- A kernel-consumable lower-bound certificate for the complete classic graph. -/
noncomputable def classicQuotientLowerBoundCertificate :
    QuotientLowerBoundCertificate classic 116 :=
  Classical.choice (checkQuotientLowerBound_sound
    classicQuotientLowerBound_checked)

/-- The checked 116-move play is globally minimal among all executable plays. -/
theorem classic116Play_minimal : classic116Play.Minimal := by
  intro other
  rw [classic116Play_length]
  exact classicQuotientLowerBoundCertificate.play_lower_bound other

end Huarongdao
