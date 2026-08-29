import Huarongdao.ClassicCertificate
import Huarongdao.MirrorQuotient
import Huarongdao.ProofGame
import Std.Tactic

namespace Huarongdao

/-- A second independently discovered 116-step play, ending at the same
    concrete goal state as `classic116Actions`. -/
def second116Actions : List Action := [
  ⟨.soldier4, .left⟩,
  ⟨.huangZhong, .down⟩,
  ⟨.soldier3, .right⟩,
  ⟨.maChao, .down⟩,
  ⟨.guanYu, .left⟩,
  ⟨.soldier2, .up⟩,
  ⟨.soldier2, .right⟩,
  ⟨.guanYu, .right⟩,
  ⟨.maChao, .up⟩,
  ⟨.soldier3, .left⟩,
  ⟨.soldier4, .left⟩,
  ⟨.huangZhong, .left⟩,
  ⟨.soldier2, .down⟩,
  ⟨.guanYu, .right⟩,
  ⟨.soldier1, .up⟩,
  ⟨.soldier4, .up⟩,
  ⟨.soldier3, .right⟩,
  ⟨.maChao, .down⟩,
  ⟨.soldier1, .left⟩,
  ⟨.guanYu, .left⟩,
  ⟨.soldier2, .down⟩,
  ⟨.zhaoYun, .down⟩,
  ⟨.zhaoYun, .down⟩,
  ⟨.caoCao, .right⟩,
  ⟨.zhangFei, .right⟩,
  ⟨.soldier1, .up⟩,
  ⟨.maChao, .up⟩,
  ⟨.soldier3, .left⟩,
  ⟨.soldier1, .up⟩,
  ⟨.maChao, .up⟩,
  ⟨.soldier4, .left⟩,
  ⟨.huangZhong, .left⟩,
  ⟨.soldier2, .left⟩,
  ⟨.zhaoYun, .down⟩,
  ⟨.guanYu, .right⟩,
  ⟨.soldier2, .up⟩,
  ⟨.huangZhong, .up⟩,
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
  ⟨.zhaoYun, .up⟩,
  ⟨.soldier3, .right⟩,
  ⟨.soldier2, .down⟩,
  ⟨.guanYu, .left⟩,
  ⟨.zhaoYun, .left⟩,
  ⟨.soldier3, .up⟩,
  ⟨.soldier2, .right⟩,
  ⟨.zhaoYun, .down⟩,
  ⟨.guanYu, .right⟩,
  ⟨.maChao, .down⟩,
  ⟨.soldier1, .left⟩,
  ⟨.guanYu, .right⟩,
  ⟨.soldier4, .up⟩,
  ⟨.zhangFei, .up⟩,
  ⟨.zhangFei, .up⟩,
  ⟨.zhaoYun, .left⟩,
  ⟨.soldier3, .left⟩,
  ⟨.soldier3, .down⟩,
  ⟨.guanYu, .down⟩,
  ⟨.caoCao, .down⟩,
  ⟨.soldier4, .right⟩,
  ⟨.soldier1, .right⟩,
  ⟨.maChao, .up⟩,
  ⟨.soldier4, .right⟩,
  ⟨.soldier1, .right⟩,
  ⟨.zhangFei, .up⟩,
  ⟨.zhaoYun, .up⟩,
  ⟨.huangZhong, .up⟩,
  ⟨.soldier2, .left⟩,
  ⟨.soldier3, .left⟩,
  ⟨.soldier2, .left⟩,
  ⟨.soldier3, .left⟩,
  ⟨.guanYu, .down⟩,
  ⟨.caoCao, .down⟩,
  ⟨.soldier4, .down⟩,
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
  ⟨.soldier4, .left⟩,
  ⟨.soldier1, .up⟩,
  ⟨.guanYu, .up⟩,
  ⟨.soldier3, .right⟩,
  ⟨.soldier3, .right⟩,
  ⟨.soldier2, .right⟩,
  ⟨.soldier2, .right⟩,
  ⟨.caoCao, .down⟩,
  ⟨.soldier1, .left⟩,
  ⟨.soldier4, .left⟩,
  ⟨.soldier1, .left⟩,
  ⟨.soldier4, .left⟩,
  ⟨.guanYu, .up⟩,
  ⟨.soldier2, .up⟩,
  ⟨.soldier2, .right⟩,
  ⟨.caoCao, .right⟩
]

theorem second116_length : second116Actions.length = 116 := by
  native_decide

theorem second116_runs :
    runMoves classic second116Actions = some classic116Goal := by
  native_decide

theorem second116_reaches_goal : goal classic116Goal = true :=
  classic116_reaches_goal

def second116Play : CertifiedPlay classic where
  actions := second116Actions
  target := classic116Goal
  executed := second116_runs
  solved := second116_reaches_goal

theorem second116Play_length : second116Play.length = 116 := by
  exact second116_length

theorem second116Play_minimal : second116Play.Minimal := by
  intro other
  rw [second116Play_length]
  exact classicQuotientLowerBoundCertificate.play_lower_bound other

theorem classic116Goal_valid : ValidState classic116Goal := by
  native_decide

/-- The sequence of equal-shape classes visited by a proof-carrying path. -/
def Path.shapeNodes {s t : State} (path : Path s t) (hs : ValidState s) :
    List ShapeState :=
  match path with
  | .nil _ => [ShapeState.ofState ⟨s, hs⟩]
  | .cons _ step tail =>
      ShapeState.ofState ⟨s, hs⟩ :: tail.shapeNodes (tryMove_preserves_validity step)

theorem Path.shapeNodes_ne_nil {s t : State} (path : Path s t) (hs : ValidState s) :
    path.shapeNodes hs ≠ [] := by
  cases path <;> simp [Path.shapeNodes]

theorem Path.shapeNodes_getLast {s t : State} (path : Path s t) (hs : ValidState s) :
    (path.shapeNodes hs).getLast (Path.shapeNodes_ne_nil path hs) =
      ShapeState.ofState ⟨t, path.target_valid hs⟩ := by
  induction path with
  | nil => simp [Path.shapeNodes]
  | @cons source middle target action step tail ih =>
      simp [Path.shapeNodes]
      rw [List.getLast_cons]
      exact ih (tryMove_preserves_validity step)

namespace CertifiedPlay

noncomputable def shapeNodes (play : CertifiedPlay start) (hs : ValidState start) :
    List ShapeState :=
  play.toSolution.path.shapeNodes hs

theorem shapeNodes_ne_nil (play : CertifiedPlay start) (hs : ValidState start) :
    play.shapeNodes hs ≠ [] :=
  Path.shapeNodes_ne_nil play.toSolution.path hs

end CertifiedPlay

/-- Two classic plays are mirror-equivalent when the shape-class node sequence
    of the second is the pointwise mirror of the first. -/
noncomputable def ClassicPlaysMirrorEquivalent
    (left right : CertifiedPlay classic) : Prop :=
  right.shapeNodes classic_valid =
    (left.shapeNodes classic_valid).map mirrorShapeState

theorem classicPlaysMirrorEquivalent_last
    {left right : CertifiedPlay classic}
    (equivalent : ClassicPlaysMirrorEquivalent left right) :
    (right.shapeNodes classic_valid).getLast
        (right.shapeNodes_ne_nil classic_valid) =
      mirrorShapeState
        ((left.shapeNodes classic_valid).getLast
          (left.shapeNodes_ne_nil classic_valid)) := by
  unfold ClassicPlaysMirrorEquivalent at equivalent
  rw [equivalent]
  rw [List.getLast_map]

theorem classic116Goal_not_mirror_fixed :
    mirrorShapeState (ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩) ≠
      ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩ := by
  intro equal
  have hsame : SameShape (mirrorState classic116Goal) classic116Goal := by
    apply ShapeState.sameShape_of_ofState_eq
    change ShapeState.ofState (mirrorValidState ⟨classic116Goal, classic116Goal_valid⟩) =
      ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩
    simpa using equal
  have hnot : ¬ SameShape (mirrorState classic116Goal) classic116Goal := by
    native_decide
  exact hnot hsame

theorem not_classicPlaysMirrorEquivalent_of_same_target
    {left right : CertifiedPlay classic}
    (leftTarget : left.target = classic116Goal)
    (rightTarget : right.target = classic116Goal) :
    ¬ ClassicPlaysMirrorEquivalent left right := by
  intro equivalent
  have hlast := classicPlaysMirrorEquivalent_last equivalent
  have hleft :
      (left.shapeNodes classic_valid).getLast
          (left.shapeNodes_ne_nil classic_valid) =
        ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩ := by
    calc
      (left.shapeNodes classic_valid).getLast
          (left.shapeNodes_ne_nil classic_valid) =
            ShapeState.ofState ⟨left.target, left.target_valid classic_valid⟩ :=
              Path.shapeNodes_getLast left.toSolution.path classic_valid
      _ = ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩ := by
        congr
        apply Subtype.ext
        exact leftTarget
  have hright :
      (right.shapeNodes classic_valid).getLast
          (right.shapeNodes_ne_nil classic_valid) =
        ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩ := by
    calc
      (right.shapeNodes classic_valid).getLast
          (right.shapeNodes_ne_nil classic_valid) =
            ShapeState.ofState ⟨right.target, right.target_valid classic_valid⟩ :=
              Path.shapeNodes_getLast right.toSolution.path classic_valid
      _ = ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩ := by
        congr
        apply Subtype.ext
        exact rightTarget
  have hmirror :
      ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩ =
        mirrorShapeState
          (ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩) := by
    calc
      ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩ =
          (right.shapeNodes classic_valid).getLast
            (right.shapeNodes_ne_nil classic_valid) := hright.symm
      _ = mirrorShapeState
            ((left.shapeNodes classic_valid).getLast
              (left.shapeNodes_ne_nil classic_valid)) := hlast
      _ = mirrorShapeState
            (ShapeState.ofState ⟨classic116Goal, classic116Goal_valid⟩) := by
              rw [hleft]
  exact classic116Goal_not_mirror_fixed hmirror.symm

/-- There are two 116-step shortest plays that are not mirror-equivalent. -/
theorem exists_two_nonmirror_shortest_plays :
    ∃ left right : CertifiedPlay classic,
      left.length = 116 ∧ right.length = 116 ∧
        ¬ ClassicPlaysMirrorEquivalent left right := by
  refine ⟨classic116Play, second116Play,
    classic116Play_length, second116Play_length, ?_⟩
  exact not_classicPlaysMirrorEquivalent_of_same_target rfl rfl

end Huarongdao
