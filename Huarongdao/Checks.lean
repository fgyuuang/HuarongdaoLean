import Huarongdao.Model

namespace Huarongdao

/-- The classic layout has not already reached the exit. -/
theorem classic_not_goal : goal classic = false := by rfl

/-- Exactly four one-cell moves are available in the classic layout. -/
theorem classic_initial_degree : (legalMoves classic).length = 4 := by rfl

end Huarongdao
