import Huarongdao.Minimality
import Std.Tactic

namespace Huarongdao

/-- A shortest path found by the Lean BFS certificate generator. -/
def classic116Actions : List Action := [
  ⟨.soldier3, .right⟩,
  ⟨.maChao, .down⟩,
  ⟨.guanYu, .left⟩,
  ⟨.soldier2, .up⟩,
  ⟨.soldier4, .left⟩,
  ⟨.huangZhong, .down⟩,
  ⟨.soldier2, .right⟩,
  ⟨.guanYu, .right⟩,
  ⟨.maChao, .up⟩,
  ⟨.soldier3, .left⟩,
  ⟨.soldier4, .left⟩,
  ⟨.huangZhong, .left⟩,
  ⟨.soldier2, .down⟩,
  ⟨.guanYu, .right⟩,
  ⟨.soldier1, .up⟩,
  ⟨.soldier2, .down⟩,
  ⟨.soldier4, .up⟩,
  ⟨.soldier3, .right⟩,
  ⟨.maChao, .down⟩,
  ⟨.soldier1, .left⟩,
  ⟨.guanYu, .left⟩,
  ⟨.zhaoYun, .down⟩,
  ⟨.zhaoYun, .down⟩,
  ⟨.caoCao, .right⟩,
  ⟨.zhangFei, .right⟩,
  ⟨.soldier1, .up⟩,
  ⟨.maChao, .up⟩,
  ⟨.soldier1, .up⟩,
  ⟨.maChao, .up⟩,
  ⟨.soldier3, .left⟩,
  ⟨.soldier4, .left⟩,
  ⟨.huangZhong, .left⟩,
  ⟨.soldier2, .left⟩,
  ⟨.zhaoYun, .down⟩,
  ⟨.guanYu, .right⟩,
  ⟨.huangZhong, .up⟩,
  ⟨.soldier2, .up⟩,
  ⟨.soldier3, .right⟩,
  ⟨.soldier3, .right⟩,
  ⟨.huangZhong, .down⟩,
  ⟨.zhangFei, .down⟩,
  ⟨.soldier1, .right⟩,
  ⟨.maChao, .up⟩,
  ⟨.soldier4, .up⟩,
  ⟨.huangZhong, .left⟩,
  ⟨.zhangFei, .down⟩,
  ⟨.zhangFei, .down⟩,
  ⟨.soldier4, .right⟩,
  ⟨.soldier4, .up⟩,
  ⟨.guanYu, .left⟩,
  ⟨.guanYu, .left⟩,
  ⟨.zhaoYun, .up⟩,
  ⟨.soldier3, .right⟩,
  ⟨.soldier2, .down⟩,
  ⟨.zhaoYun, .left⟩,
  ⟨.soldier3, .up⟩,
  ⟨.soldier2, .right⟩,
  ⟨.zhaoYun, .down⟩,
  ⟨.guanYu, .right⟩,
  ⟨.guanYu, .right⟩,
  ⟨.zhangFei, .up⟩,
  ⟨.maChao, .down⟩,
  ⟨.soldier1, .left⟩,
  ⟨.soldier4, .up⟩,
  ⟨.zhangFei, .up⟩,
  ⟨.zhaoYun, .left⟩,
  ⟨.soldier2, .left⟩,
  ⟨.soldier3, .down⟩,
  ⟨.guanYu, .down⟩,
  ⟨.caoCao, .down⟩,
  ⟨.soldier4, .right⟩,
  ⟨.soldier1, .right⟩,
  ⟨.maChao, .up⟩,
  ⟨.huangZhong, .up⟩,
  ⟨.soldier4, .right⟩,
  ⟨.soldier1, .right⟩,
  ⟨.zhangFei, .up⟩,
  ⟨.zhaoYun, .up⟩,
  ⟨.soldier2, .left⟩,
  ⟨.soldier2, .left⟩,
  ⟨.soldier3, .left⟩,
  ⟨.soldier3, .left⟩,
  ⟨.guanYu, .down⟩,
  ⟨.caoCao, .down⟩,
  ⟨.soldier1, .down⟩,
  ⟨.soldier1, .right⟩,
  ⟨.zhangFei, .right⟩,
  ⟨.zhaoYun, .up⟩,
  ⟨.zhaoYun, .up⟩,
  ⟨.caoCao, .left⟩,
  ⟨.soldier1, .down⟩,
  ⟨.soldier1, .down⟩,
  ⟨.soldier4, .down⟩,
  ⟨.soldier4, .down⟩,
  ⟨.zhangFei, .right⟩,
  ⟨.zhaoYun, .right⟩,
  ⟨.maChao, .right⟩,
  ⟨.huangZhong, .up⟩,
  ⟨.huangZhong, .up⟩,
  ⟨.caoCao, .left⟩,
  ⟨.soldier1, .left⟩,
  ⟨.soldier1, .up⟩,
  ⟨.guanYu, .up⟩,
  ⟨.soldier3, .right⟩,
  ⟨.soldier2, .right⟩,
  ⟨.soldier3, .right⟩,
  ⟨.soldier2, .right⟩,
  ⟨.caoCao, .down⟩,
  ⟨.soldier1, .left⟩,
  ⟨.soldier1, .left⟩,
  ⟨.soldier4, .left⟩,
  ⟨.soldier4, .left⟩,
  ⟨.guanYu, .up⟩,
  ⟨.soldier2, .up⟩,
  ⟨.soldier2, .right⟩,
  ⟨.caoCao, .right⟩
]

def classic116Goal : State := ⟨#[
  ⟨1, 3⟩, ⟨2, 2⟩,
  ⟨3, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩,
  ⟨0, 2⟩, ⟨3, 3⟩, ⟨3, 4⟩, ⟨1, 2⟩
]⟩

theorem classic116_length : classic116Actions.length = 116 := by
  native_decide

theorem classic116_runs :
    runMoves classic classic116Actions = some classic116Goal := by
  native_decide

theorem classic116_reaches_goal : goal classic116Goal = true := by
  native_decide

def classic116Play : CertifiedPlay classic where
  actions := classic116Actions
  target := classic116Goal
  executed := classic116_runs
  solved := classic116_reaches_goal

theorem classic116Play_length : classic116Play.length = 116 := by
  exact classic116_length

/-- The remaining bridge: any kernel-level 116 lower-bound certificate proves this play minimal. -/
theorem classic116Play_minimal_of_certificate
    (certificate : LowerBoundCertificate classic 116) :
    classic116Play.Minimal := by
  intro other
  have lower := certificate.play_lower_bound other
  rw [classic116Play_length]
  exact lower

noncomputable def classic116Path : Path classic classic116Goal :=
  Path.ofRunMoves classic116_runs

noncomputable def classic116Solution : Solution classic where
  target := classic116Goal
  path := classic116Path
  solved := classic116_reaches_goal

theorem classic_solvable : Nonempty (Solution classic) :=
  ⟨classic116Solution⟩

end Huarongdao
