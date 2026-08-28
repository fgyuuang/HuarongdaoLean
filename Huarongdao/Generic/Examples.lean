import Huarongdao.Generic.Certificates
import Std.Tactic

namespace SlidingPuzzle.Examples

open Huarongdao

/-- A non-Huarongdao 3×2 puzzle with two numbered unit blocks. -/
def tiny : PuzzleSpec where
  width := 3
  height := 2
  shapes := #[⟨1, 1⟩, ⟨1, 1⟩]
  initial := ⟨#[⟨0, 0⟩, ⟨1, 0⟩]⟩
  goal := ⟨#[some ⟨2, 0⟩, none]⟩

def tinyActions : List Action := [
  ⟨1, .down⟩,
  ⟨0, .right⟩,
  ⟨0, .right⟩
]

theorem tiny_wellFormed : wellFormed tiny = true := by native_decide

theorem tiny_actions_verified : checkSolution tiny tinyActions = true := by native_decide

theorem tiny_solvable : Nonempty (Solution tiny) := by
  have solves : Solves tiny tinyActions := checkSolution_sound tiny_actions_verified
  rw [solves_iff_nonempty_certified] at solves
  rcases solves with ⟨play, _⟩
  exact ⟨play.toSolution⟩

def tinySearch : SearchResult := search tiny ⟨1000, 20, .bfs⟩

theorem tiny_search_verified : tinySearch.verified tiny = true := by native_decide

theorem tiny_search_proves_exists : Nonempty (Solution tiny) :=
  verified_search_implies_exists tiny_search_verified

/-- The completed BFS node set is independently checked for successor closure. -/
theorem tiny_search_closed :
    tinySearch.graph.checkClosedGraph tiny = true := by
  native_decide

/-- Therefore every state reachable in the mathematical transition system is
    present in the finite BFS node array. -/
theorem tiny_search_contains_every_reachable
    (state : State) (reachable : Reachable tiny tiny.initial state) :
    state ∈ tinySearch.graph.states.toList :=
  StateGraph.checkClosedGraph_sound tiny_search_closed state reachable

/-- A one-block puzzle whose unique shortest completion has one primitive move. -/
def oneStep : PuzzleSpec where
  width := 2
  height := 1
  shapes := #[⟨1, 1⟩]
  initial := ⟨#[⟨0, 0⟩]⟩
  goal := Goal.complete ⟨#[⟨1, 0⟩]⟩

def oneStepActions : List Action := [⟨0, .right⟩]

theorem oneStep_verified : VerifiedPath oneStep oneStepActions := by
  unfold VerifiedPath
  native_decide

/-- The Boolean goal indicator is enough to certify the lower bound one:
    it starts at zero, every move raises it by at most one, and every goal has
    rank one. -/
def oneStepLowerBound : LowerBoundCertificate oneStep 1 where
  rank := fun state => if goalMatches oneStep state then 1 else 0
  startRank := by native_decide
  stepRank := by
    intro source target action executed
    by_cases targetGoal : goalMatches oneStep target = true <;>
      by_cases sourceGoal : goalMatches oneStep source = true <;>
      simp [targetGoal, sourceGoal]
  goalRank := by
    intro target solved
    change 1 ≤ if goalMatches oneStep target then 1 else 0
    simp [solved]

theorem oneStep_is_shortest :
    IsShortestSolution oneStep oneStepActions := by
  apply shortest_of_verified_path_and_lower_bound oneStep_verified
  simpa [oneStepActions] using oneStepLowerBound

end SlidingPuzzle.Examples
