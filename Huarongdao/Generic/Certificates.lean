import Huarongdao.Generic.Verification
import Std.Tactic

namespace SlidingPuzzle

namespace StateGraph

/-- A finite node set is closed when it contains the initial state and every
    legal successor of every contained state. -/
def ClosedUnderMoves (spec : PuzzleSpec) (graph : StateGraph) : Prop :=
  spec.initial ∈ graph.states.toList ∧
  ∀ {source target : State} {action : Action},
    source ∈ graph.states.toList →
    tryMove spec source action.block action.direction = some target →
    target ∈ graph.states.toList

/-- Executable closure check. It deliberately checks the transition semantics
    again instead of trusting the exported edge array. -/
def checkClosedGraph (spec : PuzzleSpec) (graph : StateGraph) : Bool :=
  graph.states.toList.contains spec.initial &&
  graph.states.toList.all fun source =>
    (legalMoves spec source).all fun move =>
      graph.states.toList.contains move.2

theorem checkClosedGraph_closed
    {spec : PuzzleSpec} {graph : StateGraph}
    (checked : graph.checkClosedGraph spec = true) :
    graph.ClosedUnderMoves spec := by
  unfold checkClosedGraph at checked
  rw [Bool.and_eq_true] at checked
  constructor
  · simpa using checked.1
  · intro source target action sourceMem executed
    have sourceChecked :=
      (List.all_eq_true.mp checked.2) source sourceMem
    have moveMem : (action, target) ∈ legalMoves spec source :=
      legalMoves_complete executed
    have targetChecked :=
      (List.all_eq_true.mp sourceChecked) (action, target) moveMem
    simpa using targetChecked

theorem ClosedUnderMoves.reachable_mem
    {spec : PuzzleSpec} {graph : StateGraph}
    (closed : graph.ClosedUnderMoves spec)
    {source target : State}
    (sourceMem : source ∈ graph.states.toList)
    (reachable : Reachable spec source target) :
    target ∈ graph.states.toList := by
  induction reachable with
  | refl => exact sourceMem
  | tail step _ ih =>
      rcases step with ⟨action, executed⟩
      exact ih (closed.2 sourceMem executed)

/-- A successful finite closure check proves that no state reachable from the
    initial state is missing from the supplied node set. -/
theorem checkClosedGraph_sound
    {spec : PuzzleSpec} {graph : StateGraph}
    (checked : graph.checkClosedGraph spec = true) :
    ∀ state, Reachable spec spec.initial state →
      state ∈ graph.states.toList := by
  intro state reachable
  have closed := graph.checkClosedGraph_closed checked
  exact closed.reachable_mem closed.1 reachable

/-- Check that none of the supplied nodes satisfies the goal predicate. -/
def checkNoGoal (spec : PuzzleSpec) (graph : StateGraph) : Bool :=
  graph.states.toList.all fun state => !goalMatches spec state

theorem checkNoGoal_sound
    {spec : PuzzleSpec} {graph : StateGraph}
    (checked : graph.checkNoGoal spec = true)
    {state : State} (member : state ∈ graph.states.toList) :
    goalMatches spec state = false := by
  unfold checkNoGoal at checked
  have stateChecked := (List.all_eq_true.mp checked) state member
  simpa using stateChecked

/-- Closure plus absence of a listed goal is a proof that no reachable goal
    exists. This is the certificate-level form of an `unreachable` result. -/
theorem no_reachable_goal_of_closed_graph
    {spec : PuzzleSpec} {graph : StateGraph}
    (closed : graph.checkClosedGraph spec = true)
    (noGoal : graph.checkNoGoal spec = true) :
    ¬ ∃ state, Reachable spec spec.initial state ∧
      goalMatches spec state = true := by
  rintro ⟨state, reachable, solved⟩
  have member := checkClosedGraph_sound closed state reachable
  have notSolved := checkNoGoal_sound noGoal member
  rw [solved] at notSolved
  contradiction

end StateGraph

/-- A local ranking argument proving that every solution has length at least
    `bound`. A legal move may increase the rank by at most one. -/
structure LowerBoundCertificate (spec : PuzzleSpec) (bound : Nat) where
  rank : State → Nat
  startRank : rank spec.initial = 0
  stepRank : ∀ {source target : State} {action : Action},
    tryMove spec source action.block action.direction = some target →
    rank target ≤ rank source + 1
  goalRank : ∀ {target : State},
    goalMatches spec target = true → bound ≤ rank target

namespace LowerBoundCertificate

theorem path_rank_le
    (certificate : LowerBoundCertificate spec bound)
    (path : Path spec source target) :
    certificate.rank target ≤ certificate.rank source + path.length := by
  induction path with
  | nil => simp [Path.length]
  | cons _ executed _ ih =>
      have headRank := certificate.stepRank executed
      simp only [Path.length]
      omega

theorem initial_path_lower_bound
    (certificate : LowerBoundCertificate spec bound)
    (path : Path spec spec.initial target)
    (solved : goalMatches spec target = true) :
    bound ≤ path.length := by
  have pathRank := certificate.path_rank_le path
  have goalRank := certificate.goalRank solved
  rw [certificate.startRank] at pathRank
  omega

theorem runMoves_rank_le
    (certificate : LowerBoundCertificate spec bound)
    {source target : State} {actions : List Action}
    (executed : runMoves spec source actions = some target) :
    certificate.rank target ≤ certificate.rank source + actions.length := by
  induction actions generalizing source with
  | nil =>
      simp [runMoves] at executed
      subst target
      simp
  | cons action rest ih =>
      cases moved : tryMove spec source action.block action.direction with
      | none => simp [runMoves, moved] at executed
      | some next =>
          simp [runMoves, moved] at executed
          have tailRank := ih executed
          have headRank := certificate.stepRank moved
          simp only [List.length_cons]
          omega

theorem solves_lower_bound
    (certificate : LowerBoundCertificate spec bound)
    {actions : List Action}
    (solves : Solves spec actions) :
    bound ≤ actions.length := by
  rcases solves with ⟨target, executed, solved⟩
  have pathRank := certificate.runMoves_rank_le executed
  have goalRank := certificate.goalRank solved
  rw [certificate.startRank] at pathRank
  omega

end LowerBoundCertificate

/-- The action list has been independently replayed and reaches a goal. -/
def VerifiedPath (spec : PuzzleSpec) (actions : List Action) : Prop :=
  checkSolution spec actions = true

/-- An executable solution is shortest when no other executable solution uses
    fewer primitive actions. -/
def IsShortestSolution (spec : PuzzleSpec) (actions : List Action) : Prop :=
  Solves spec actions ∧
  ∀ other : List Action, Solves spec other → actions.length ≤ other.length

/-- A verified path supplies the upper bound; a matching ranking certificate
    supplies the lower bound. Together they prove global shortestness. -/
theorem shortest_of_verified_path_and_lower_bound
    {spec : PuzzleSpec} {actions : List Action}
    (verified : VerifiedPath spec actions)
    (certificate : LowerBoundCertificate spec actions.length) :
    IsShortestSolution spec actions := by
  constructor
  · exact checkSolution_sound verified
  · intro other otherSolves
    exact certificate.solves_lower_bound otherSolves

namespace Solution

def length (solution : Solution spec) : Nat := solution.path.length

def Minimal (solution : Solution spec) : Prop :=
  ∀ other : Solution spec, solution.length ≤ other.length

end Solution

theorem Solution.minimal_of_lower_bound
    (solution : Solution spec)
    (certificate : LowerBoundCertificate spec solution.length) :
    solution.Minimal := by
  intro other
  exact certificate.initial_path_lower_bound other.path other.solved

end SlidingPuzzle
