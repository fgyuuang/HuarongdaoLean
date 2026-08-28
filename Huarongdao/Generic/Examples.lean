import Huarongdao.Generic.Certificates
import Huarongdao.Generic.FiniteMathlibGraph
import Mathlib.Tactic

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
    simp [solved]

theorem oneStep_is_shortest :
    IsShortestSolution oneStep oneStepActions := by
  apply shortest_of_verified_path_and_lower_bound oneStep_verified
  simpa [oneStepActions] using oneStepLowerBound

/-- A complete BFS run used to exercise the finite Mathlib graph bridge. -/
def oneStepSearch : SearchResult :=
  search oneStep ⟨10, 5, .bfs⟩

def oneStepTargetState : State :=
  ⟨#[⟨1, 0⟩]⟩

/-- An explicit finite presentation of the graph computed by `oneStepSearch`.
    Large exported graphs use the same data shape, but obtain these arrays
    from files rather than reducing the search inside the kernel. -/
def oneStepFiniteGraph : StateGraph where
  states := #[oneStep.initial, oneStepTargetState]
  distance := #[0, 1]
  edges := #[
    ⟨0, 1, ⟨0, .right⟩⟩,
    ⟨1, 0, ⟨0, .left⟩⟩
  ]
  expanded := 2
  generated := 2
  complete := true
  truncated := false

/-- The executable search agrees with the explicit graph presentation used by
    the proof-facing bridge. -/
theorem oneStep_search_matches_finite_graph :
    oneStepSearch.graph.states = oneStepFiniteGraph.states ∧
    oneStepSearch.graph.distance = oneStepFiniteGraph.distance ∧
    oneStepSearch.graph.edges = oneStepFiniteGraph.edges ∧
    oneStepSearch.graph.complete = oneStepFiniteGraph.complete ∧
    oneStepSearch.graph.truncated = oneStepFiniteGraph.truncated := by
  native_decide

def oneStepFiniteGraphCertificate :
    StateGraph.FiniteGraphCertificate oneStep oneStepFiniteGraph where
  root := ⟨0, by native_decide⟩
  root_eq_initial := by native_decide
  valid := by
    intro vertex
    fin_cases vertex <;> unfold ValidState <;> native_decide
  nodup := by native_decide

def oneStepBfsDistanceCertificate :
    StateGraph.BfsDistanceCertificate oneStep oneStepFiniteGraph where
  finite := oneStepFiniteGraphCertificate
  distances := ⟨by native_decide⟩
  root_distance := by native_decide
  step := by
    intro source target _adjacent
    fin_cases source <;> fin_cases target <;> native_decide
  predecessor := by
    intro vertex notRoot
    fin_cases vertex
    · exact (notRoot rfl).elim
    · refine ⟨⟨0, by native_decide⟩, ?_, by native_decide⟩
      change Step oneStep oneStep.initial oneStepTargetState
      exact ⟨⟨0, .right⟩, by native_decide⟩

def oneStepGoalVertex : oneStepFiniteGraph.Vertex :=
  ⟨1, by native_decide⟩

/-- The executable BFS label and Mathlib's shortest-walk distance agree on an
    actual finite search result. -/
theorem oneStep_mathlib_dist_eq_one :
    oneStepFiniteGraphCertificate.finiteSimpleGraph.dist
        oneStepFiniteGraphCertificate.root oneStepGoalVertex = 1 := by
  exact
    (oneStepBfsDistanceCertificate.finiteSimpleGraph_dist_eq_arrayDistance
      oneStepGoalVertex).trans (by native_decide)

/-- Closure upgrades the finite distance theorem to the unrestricted semantic
    puzzle graph, rather than only the exported induced subgraph. -/
theorem oneStep_full_mathlib_dist_eq_one :
    (puzzleSimpleGraph oneStep).dist
        (oneStepFiniteGraphCertificate.vertexEmbedding
          oneStepFiniteGraphCertificate.root)
        (oneStepFiniteGraphCertificate.vertexEmbedding oneStepGoalVertex) = 1 := by
  exact
    (oneStepBfsDistanceCertificate.puzzleSimpleGraph_dist_eq_arrayDistance
      (by native_decide) oneStepGoalVertex).trans (by native_decide)

/-- Mathlib's bridge predicate is now directly executable on the certified
    finite state graph. -/
theorem oneStep_transition_is_bridge :
    oneStepFiniteGraphCertificate.finiteSimpleGraph.IsBridge
      s(oneStepFiniteGraphCertificate.root, oneStepGoalVertex) := by
  rw [SimpleGraph.isBridge_iff]
  native_decide

end SlidingPuzzle.Examples
