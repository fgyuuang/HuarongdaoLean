import Huarongdao.Generic.Search
import Huarongdao.Generic.Transition

namespace SlidingPuzzle

/-- Every checked route displayed in the generic graph explorer is reachable. -/
theorem GraphPath.toReachable (path : GraphPath spec graph source target) :
    Reachable spec source target := by
  induction path with
  | nil => exact .refl _
  | cons edge source_eq target_eq checked _ ih =>
      have executed := StateGraph.checkEdge_sound checked
      rw [source_eq, target_eq] at executed
      exact .tail ⟨edge.action, executed⟩ ih

/-- A verified search result exhibits a goal node in the concrete reachable graph. -/
theorem verified_search_exhibits_reachable_goal
    {spec : PuzzleSpec} {result : SearchResult}
    (verified : result.verified spec = true) :
    ∃ target : State,
      Reachable spec spec.initial target ∧ goalMatches spec target = true := by
  rcases verified_search_implies_exists verified with ⟨solution⟩
  exact ⟨solution.target, solution.target_reachable, solution.solved⟩

/-- The entire requested chain, retaining the action witness as well. -/
theorem verified_search_chain
    {spec : PuzzleSpec} {result : SearchResult}
    (verified : result.verified spec = true) :
    ∃ actions target,
      runMoves spec spec.initial actions = some target ∧
      Reachable spec spec.initial target ∧
      goalMatches spec target = true := by
  have solves := result.verified_solution verified
  rcases solves with ⟨target, executed, solved⟩
  let path := Path.ofRunMoves executed
  exact ⟨result.actions, target, executed, path.toReachable, solved⟩

end SlidingPuzzle
