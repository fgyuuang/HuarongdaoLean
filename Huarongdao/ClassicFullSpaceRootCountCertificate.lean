import Huarongdao.ClassicFullSpace

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Cached root-count certificate

`fullSpaceRun` is the executable DFS presentation of the full placement
enumeration.  The semantic cardinality theorem needs the size of its component
index (`roots.size`); this module computes that fact once and exports the
opaque proof through its compiled `.olean`.
-/

theorem fullSpaceRun_roots_size_checked :
    fullSpaceRun.roots.size = 898 := by
  set_option maxHeartbeats 0 in
  native_decide

end ClassicFullSpace
end Huarongdao
