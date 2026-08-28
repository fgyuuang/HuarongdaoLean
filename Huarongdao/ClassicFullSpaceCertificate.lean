import Huarongdao.ClassicFullSpace

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/--
The full-space certificate is intentionally isolated from the default library
build. It performs the complete 65,880-state traversal during compilation.
-/
theorem fullSpace_checked :
    checkFullSpace = true := by
  set_option maxHeartbeats 0 in
  native_decide

theorem fullSpace_facts : fullSpaceClaims :=
  of_decide_eq_true fullSpace_checked

/-- A projection-friendly form of the shared native certificate. -/
theorem analysis_facts :
    analyze.stateCount = 65880 ∧
    analyze.allValid = true ∧
    analyze.keysUnique = true ∧
    analyze.closed = true ∧
    analyze.summaries.size = 898 ∧
    analyze.coveredCount = 65880 ∧
    analyze.classicSize = 25955 := by
  simpa only [fullSpaceClaims] using fullSpace_facts

/-- The constructive enumeration contains exactly 65,880 representatives. -/
theorem analysis_stateCount : analyze.stateCount = 65880 :=
  analysis_facts.1

/-- Every generated representative is a valid classic board. -/
theorem analysis_allValid : analyze.allValid = true :=
  analysis_facts.2.1

/-- No two generated representatives denote the same equal-shape state. -/
theorem analysis_keysUnique : analyze.keysUnique = true :=
  analysis_facts.2.2.1

/-- Every legal successor of a generated representative is represented. -/
theorem analysis_closed : analyze.closed = true :=
  analysis_facts.2.2.2.1

/-- The deterministic traversal produces exactly 898 component summaries. -/
theorem analysis_componentCount : analyze.summaries.size = 898 :=
  analysis_facts.2.2.2.2.1

/-- The computed components cover all 65,880 generated states. -/
theorem analysis_coveredCount : analyze.coveredCount = 65880 :=
  analysis_facts.2.2.2.2.2.1

/-- The class containing the traditional initial layout has 25,955 states. -/
theorem analysis_classicSize : analyze.classicSize = 25955 :=
  analysis_facts.2.2.2.2.2.2

end ClassicFullSpace
end Huarongdao
