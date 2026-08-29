import Huarongdao.ShortestPathTopology
import Huarongdao.MirrorQuotient

namespace Huarongdao

/-!
This module packages the independently checked alternative shortest play from
`ShortestPathTopology` under the names used by the finite-graph research.
-/

/-- A second 116-step play obtained by swapping two commuting initial moves. -/
def second116Actions : List Action :=
  classic116AlternativeActions

theorem second116_length : second116Actions.length = 116 := by
  exact classic116Alternative_length

theorem second116_runs :
    runMoves classic second116Actions = some classic116Goal := by
  exact classic116Alternative_runs

theorem second116_reaches_goal : goal classic116Goal = true :=
  classic116_reaches_goal

def second116Play : CertifiedPlay classic :=
  classic116AlternativePlay

theorem second116Play_length : second116Play.length = 116 := by
  exact second116_length

theorem second116Play_minimal : second116Play.Minimal := by
  intro play
  exact classic116AlternativePlay_minimal play

/-- The sequence of equal-shape classes visited by a proof-carrying path. -/
def Path.shapeNodes {s t : State} (path : Path s t) (hs : ValidState s) :
    List ShapeState :=
  match path with
  | .nil _ => [ShapeState.ofState ⟨s, hs⟩]
  | .cons _ step tail =>
      ShapeState.ofState ⟨s, hs⟩ ::
        tail.shapeNodes (tryMove_preserves_validity step)

namespace CertifiedPlay

noncomputable def shapeNodes
    (play : CertifiedPlay start) (hs : ValidState start) :
    List ShapeState :=
  play.toSolution.path.shapeNodes hs

end CertifiedPlay

/--
Two classic plays are mirror-equivalent when their quotient-node sequences are
pointwise mirrors and their concrete endpoints have mirror-equivalent shapes.
The endpoint clause is mathematically redundant for a fully developed path-map
theorem, but records the required invariant explicitly and keeps this finite
certificate independent of a proof about `List.getLast`.
-/
noncomputable def ClassicPlaysMirrorEquivalent
    (left right : CertifiedPlay classic) : Prop :=
  right.shapeNodes classic_valid =
      (left.shapeNodes classic_valid).map mirrorShapeState ∧
    SameShape (mirrorState left.target) right.target

theorem not_classicPlaysMirrorEquivalent_of_same_target
    {left right : CertifiedPlay classic}
    (leftTarget : left.target = classic116Goal)
    (rightTarget : right.target = classic116Goal) :
    ¬ ClassicPlaysMirrorEquivalent left right := by
  intro equivalent
  have endpoint := equivalent.2
  rw [leftTarget, rightTarget] at endpoint
  exact
    (by native_decide :
      ¬ SameShape (mirrorState classic116Goal) classic116Goal) endpoint

/-- There are two 116-step shortest plays that are not mirror-equivalent. -/
theorem exists_two_nonmirror_shortest_plays :
    ∃ left right : CertifiedPlay classic,
      left.length = 116 ∧ right.length = 116 ∧
        ¬ ClassicPlaysMirrorEquivalent left right := by
  refine ⟨classic116Play, second116Play,
    classic116Play_length, second116Play_length, ?_⟩
  exact not_classicPlaysMirrorEquivalent_of_same_target rfl rfl

end Huarongdao
