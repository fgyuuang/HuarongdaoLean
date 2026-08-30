import Huarongdao.ClassicFullSpaceSoundness

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Finite replay certificate for the full DFS run

This is intentionally an offline/heavy module.  The proposition below is the
single executable check which turns the cached `componentSummariesOf` output
into the finite side of `ComponentRun.Lawful`.  Downstream files should
consume `fullSpaceRun_checkFinite_checked` from the compiled `.olean` instead
of introducing another `native_decide`.
-/

theorem fullSpaceRun_checkFinite_checked :
    ComponentRun.Lawful.checkFinite
      allShapeStates fullSpaceRun = true := by
  set_option maxHeartbeats 0 in
  native_decide

end ClassicFullSpace
end Huarongdao
