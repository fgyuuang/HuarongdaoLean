import Huarongdao.Generic.Search
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

end SlidingPuzzle.Examples
