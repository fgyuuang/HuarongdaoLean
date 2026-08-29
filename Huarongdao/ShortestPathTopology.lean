import Huarongdao.ClassicCertificate
import Huarongdao.LocalTopology
import Huarongdao.StateSpaceConnectivity
import Huarongdao.StateSpaceAnalysis
import Std.Tactic

namespace Huarongdao
namespace StateSpace
namespace Task

universe u v

variable {State : Type u} {Action : Type v}

/--
An island is a pair of different equal-length walks with the same entry and
exit.  The optional interior-disjointness field makes the picture a genuine
ring rather than two paths that merely overlap.
-/
structure RingIsland (task : Task State Action) (entry exit : State) where
  upper : task.Walk entry exit
  lower : task.Walk entry exit
  positive : 0 < upper.length
  equalLength : upper.length = lower.length
  distinct : upper.actions ≠ lower.actions
  interiorDisjoint :
    ∀ state,
      state ∈ upper.states →
      state ∈ lower.states →
      state = entry ∨ state = exit

namespace RingIsland

/-- The two arms of an island form a closed walk when the task is reversible. -/
theorem closedWalk
    (reversible : task.Reversible)
    (island : RingIsland task entry exit) :
    ∃ walk : task.Walk entry entry,
      walk.length = island.upper.length + island.lower.length := by
  let walk := island.upper.append (reversible.reverseWalk island.lower)
  refine ⟨walk, ?_⟩
  simp [walk, Task.Reversible.reverseWalk_length]

end RingIsland

/--
Splicing either arm of a ring island into a common prefix and suffix gives
two shortest walks.  This is the formal version of "branch, travel around the
island, and merge again".
-/
theorem two_shortest_walks_of_ring_island
    (shortest : task.ShortestWalkLength source target total)
    (stem : task.Walk source entry)
    (island : RingIsland task entry exit)
    (tailWalk : task.Walk exit target)
    (leftLength :
      ((stem.append island.upper).append tailWalk).length = total) :
    ∃ left right : task.Walk source target,
      left.length = total ∧
      right.length = total ∧
      left.actions ≠ right.actions ∧
      (∀ candidate, task.HasWalkLength source target candidate →
        total ≤ candidate) ∧
      (∀ candidate, task.HasWalkLength source target candidate →
        total ≤ candidate) := by
  let left := (stem.append island.upper).append tailWalk
  let right := (stem.append island.lower).append tailWalk
  have rightLength : right.length = total := by
    calc
      right.length =
          (stem.length + island.lower.length) + tailWalk.length := by
            simp [right, Task.Walk.length_append]
      _ = (stem.length + island.upper.length) + tailWalk.length := by
        rw [island.equalLength]
      _ = left.length := by
        simp [left, Task.Walk.length_append]
      _ = total := leftLength
  have actionsDifferent : left.actions ≠ right.actions := by
    intro equal
    apply island.distinct
    have reassociated :
        stem.actions ++ island.upper.actions ++ tailWalk.actions =
          stem.actions ++ island.lower.actions ++ tailWalk.actions := by
      simpa [left, right, Task.Walk.actions_append, List.append_assoc] using equal
    apply List.append_right_injective stem.actions
    apply List.append_left_injective tailWalk.actions
    simpa [List.append_assoc] using reassociated
  exact ⟨left, right, leftLength, rightLength, actionsDifferent,
    shortest.2, shortest.2⟩

end Task
end StateSpace
end Huarongdao

namespace Huarongdao

def classicSoldier3Right : Action := ⟨.soldier3, .right⟩
def classicSoldier4Left : Action := ⟨.soldier4, .left⟩

def classicAfterSoldier3Right : State := ⟨#[
  ⟨1, 0⟩, ⟨1, 2⟩,
  ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨3, 2⟩,
  ⟨1, 3⟩, ⟨2, 3⟩, ⟨1, 4⟩, ⟨3, 4⟩
]⟩

def classicAfterSoldier4Left : State := ⟨#[
  ⟨1, 0⟩, ⟨1, 2⟩,
  ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨3, 2⟩,
  ⟨1, 3⟩, ⟨2, 3⟩, ⟨0, 4⟩, ⟨2, 4⟩
]⟩

def classicAfterBothSoldierMoves : State := ⟨#[
  ⟨1, 0⟩, ⟨1, 2⟩,
  ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨3, 2⟩,
  ⟨1, 3⟩, ⟨2, 3⟩, ⟨1, 4⟩, ⟨2, 4⟩
]⟩

theorem classic_soldier3_right_step :
    tryMove classic .soldier3 .right =
      some classicAfterSoldier3Right := by
  native_decide

theorem classic_soldier4_left_step :
    tryMove classic .soldier4 .left =
      some classicAfterSoldier4Left := by
  native_decide

theorem classic_soldier4_left_after_soldier3 :
    tryMove classicAfterSoldier3Right .soldier4 .left =
      some classicAfterBothSoldierMoves := by
  native_decide

theorem classic_soldier3_right_after_soldier4 :
    tryMove classicAfterSoldier4Left .soldier3 .right =
      some classicAfterBothSoldierMoves := by
  native_decide

def classicUpperIsland :
    StateSpace.classicTask.Walk classic classicAfterBothSoldierMoves :=
  .cons classicSoldier3Right classic_soldier3_right_step
    (.cons classicSoldier4Left classic_soldier4_left_after_soldier3
      (.nil classicAfterBothSoldierMoves))

def classicLowerIsland :
    StateSpace.classicTask.Walk classic classicAfterBothSoldierMoves :=
  .cons classicSoldier4Left classic_soldier4_left_step
    (.cons classicSoldier3Right classic_soldier3_right_after_soldier4
      (.nil classicAfterBothSoldierMoves))

def classic_initial_ring_island :
    StateSpace.Task.RingIsland
      StateSpace.classicTask classic classicAfterBothSoldierMoves :=
  by
    refine {
      upper := classicUpperIsland
      lower := classicLowerIsland
      positive := by native_decide
      equalLength := by native_decide
      distinct := by native_decide
      interiorDisjoint := ?_
    }
    intro state upperMem lowerMem
    simp [classicUpperIsland, classicLowerIsland,
      StateSpace.Task.Walk.states] at upperMem lowerMem
    rcases upperMem with rfl | rfl | rfl
    · rcases lowerMem with h | h | h
      · exact Or.inl h
      · exact ((by native_decide :
          classic ≠ classicAfterSoldier4Left) h).elim
      · exact ((by native_decide :
          classic ≠ classicAfterBothSoldierMoves) h).elim
    · rcases lowerMem with h | h | h
      · exact ((by native_decide :
          classicAfterSoldier3Right ≠ classic) h).elim
      · exact ((by native_decide :
          classicAfterSoldier3Right ≠ classicAfterSoldier4Left) h).elim
      · exact ((by native_decide :
          classicAfterSoldier3Right ≠ classicAfterBothSoldierMoves) h).elim
    · rcases lowerMem with h | h | h
      · exact ((by native_decide :
          classicAfterBothSoldierMoves ≠ classic) h).elim
      · exact ((by native_decide :
          classicAfterBothSoldierMoves ≠ classicAfterSoldier4Left) h).elim
      · exact Or.inr h

def swapAdjacentAt3 (actions : List Action) : List Action :=
  match actions with
  | first :: second :: third :: fourth :: fifth :: rest =>
      first :: second :: third :: fifth :: fourth :: rest
  | _ => actions

def classic116AlternativeActions : List Action :=
  swapAdjacentAt3 classic116Actions

theorem classic116Alternative_length :
    classic116AlternativeActions.length = 116 := by
  native_decide

theorem classic116Alternative_runs :
    runMoves classic classic116AlternativeActions =
      some classic116Goal := by
  native_decide

theorem classic116Alternative_different :
    classic116AlternativeActions ≠ classic116Actions := by
  native_decide

def classic116AlternativePlay : CertifiedPlay classic where
  actions := classic116AlternativeActions
  target := classic116Goal
  executed := classic116Alternative_runs
  solved := classic116_reaches_goal

theorem every_certified_classic_play_has_at_least_116_moves
    (play : CertifiedPlay classic) :
    116 ≤ play.length := by
  rw [← classic116Play_length]
  exact classic116Play_minimal play

theorem classic116AlternativePlay_minimal :
    ∀ play : CertifiedPlay classic,
      classic116AlternativePlay.length ≤ play.length := by
  intro play
  change classic116AlternativeActions.length ≤ play.length
  rw [classic116Alternative_length]
  exact every_certified_classic_play_has_at_least_116_moves play

theorem classic116Play_minimal_certified :
    ∀ play : CertifiedPlay classic,
      classic116Play.length ≤ play.length := by
  intro play
  change classic116Actions.length ≤ play.length
  rw [classic116_length]
  exact every_certified_classic_play_has_at_least_116_moves play

theorem classic_shortest_path_not_unique :
    ∃ left right : CertifiedPlay classic,
      left.length = 116 ∧
      right.length = 116 ∧
      left.actions ≠ right.actions ∧
      (∀ play : CertifiedPlay classic, left.length ≤ play.length) ∧
      (∀ play : CertifiedPlay classic, right.length ≤ play.length) := by
  refine ⟨classic116Play, classic116AlternativePlay, ?_, ?_, ?_, ?_, ?_⟩
  · exact classic116Play_length
  · exact classic116Alternative_length
  · exact Ne.symm classic116Alternative_different
  · exact classic116Play_minimal_certified
  · intro play
    exact classic116AlternativePlay_minimal play

end Huarongdao
