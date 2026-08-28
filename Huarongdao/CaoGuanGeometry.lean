import Huarongdao.Bottleneck
import Huarongdao.ClassicSolution

namespace Huarongdao

/--
The geometric reading of "Cao Cao is below Guan Yu": Cao Cao starts on a
strictly lower row, and the two rectangular pieces have overlapping horizontal
projections.  The board convention has `y = 0` at the top, so larger `y` means
lower on the board.
-/
def CaoBelowGuanYu (state : State) : Prop :=
  let cao := state.pos .caoCao
  let guan := state.pos .guanYu
  guan.y < cao.y ∧
    guan.x < cao.x + 2 ∧
    cao.x < guan.x + 2

theorem valid_goal_caoBelowGuanYu {state : State}
    (validState : ValidState state) (goalState : goal state = true) :
    CaoBelowGuanYu state := by
  have hvalid : inBounds state = true ∧ noOverlap state = true := by
    simpa [ValidState, valid] using validState
  have hcao : state.pos .caoCao = ⟨1, 3⟩ :=
    (goal_eq_true_iff state).mp goalState
  have hboundAll := hvalid.1
  unfold inBounds at hboundAll
  rw [Bool.and_eq_true] at hboundAll
  have hguanBounds :=
    (List.all_eq_true.mp hboundAll.2)
      Piece.guanYu (Piece.mem_all Piece.guanYu)
  rw [Bool.and_eq_true] at hguanBounds
  have hguanX : (state.pos .guanYu).x + 2 ≤ 4 := by
    simpa [Piece.shape] using (of_decide_eq_true hguanBounds.1)
  have hguanY : (state.pos .guanYu).y + 1 ≤ 5 := by
    simpa [Piece.shape] using (of_decide_eq_true hguanBounds.2)
  have hpair :=
    (List.all_eq_true.mp
      (List.all_eq_true.mp hvalid.2 Piece.caoCao (Piece.mem_all Piece.caoCao))
      Piece.guanYu (Piece.mem_all Piece.guanYu))
  rcases hguan : state.pos .guanYu with ⟨gx, gy⟩
  rw [hguan] at hguanX hguanY
  simp at hguanX hguanY
  unfold CaoBelowGuanYu
  rw [hguan, hcao]
  change gy < 3 ∧ gx < 3 ∧ 1 < gx + 2
  have hbelowY : gy < 3 := by
    have hpair' := hpair
    simp [occupiedCells, Piece.shape, hguan, hcao] at hpair'
    by_cases hgy : gy ≤ 2
    · omega
    have hgy' : gy = 3 ∨ gy = 4 := by omega
    rcases hgy' with hgy3 | hgy4
    · subst gy
      have hgx : gx ≤ 2 := by omega
      have hgxCases : gx = 0 ∨ gx = 1 ∨ gx = 2 := by omega
      rcases hgxCases with rfl | rfl | rfl
      · have h := hpair' 0 (by decide) 0 (by decide) 1 (by decide)
        simp at h
      · have h := hpair' 0 (by decide) 0 (by decide) 0 (by decide)
        simp at h
      · have h := hpair' 0 (by decide) 1 (by decide) 0 (by decide)
        simp at h
    · subst gy
      have hgx : gx ≤ 2 := by omega
      have hgxCases : gx = 0 ∨ gx = 1 ∨ gx = 2 := by omega
      rcases hgxCases with rfl | rfl | rfl
      · have h := hpair' 1 (by decide) 0 (by decide) 1 (by decide)
        simp at h
      · have h := hpair' 1 (by decide) 0 (by decide) 0 (by decide)
        simp at h
      · have h := hpair' 1 (by decide) 1 (by decide) 0 (by decide)
        simp at h
  exact ⟨hbelowY, by omega, by omega⟩

theorem solution_visits_caoBelowGuanYu (solution : Solution classic) :
    solution.path.Visits CaoBelowGuanYu := by
  apply solution.path.visits_target CaoBelowGuanYu
  exact valid_goal_caoBelowGuanYu
    (solution.target_valid classic_valid) solution.solved

theorem classic_solutionGate_caoBelowGuanYu :
    SolutionGate classic CaoBelowGuanYu := by
  intro solution
  exact solution_visits_caoBelowGuanYu solution

theorem classic116Goal_caoBelowGuanYu :
    CaoBelowGuanYu classic116Goal := by
  exact valid_goal_caoBelowGuanYu
    (classic116Solution.target_valid classic_valid)
    classic116_reaches_goal

end Huarongdao
