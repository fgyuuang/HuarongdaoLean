import Huarongdao.Enumeration
import Huarongdao.Symmetry
import Std.Data.HashMap
import Std.Data.HashSet

namespace Huarongdao
structure Edge where
  source : Nat
  target : Nat
  piece : Piece
  direction : Direction
  deriving Repr, DecidableEq, BEq

structure Graph where
  states : Array State
  edges : Array Edge
  distance : Array Nat

def enumerate (start : State) : Graph := Id.run do
  let mut states := #[start]
  let mut edges := #[]
  let mut distance := #[0]
  let mut known : Std.HashMap String Nat := {}
  known := known.insert start.key 0
  let mut cursor := 0
  while cursor < states.size do
    let state := states.getD cursor start
    let depth := distance.getD cursor 0
    for (piece, direction, next) in legalMoves state do
      let target ← match known.get? next.key with
        | some id => pure id
        | none =>
          let id := states.size
          states := states.push next
          distance := distance.push (depth + 1)
          known := known.insert next.key id
          pure id
      edges := edges.push ⟨cursor, target, piece, direction⟩
    cursor := cursor + 1
  return ⟨states, edges, distance⟩

def Graph.sourceState (g : Graph) (edge : Edge) : State :=
  g.states.getD edge.source classic

def Graph.targetState (g : Graph) (edge : Edge) : State :=
  g.states.getD edge.target classic

/-- Independently re-run an edge and compare its geometric target. -/
def checkEdge (g : Graph) (edge : Edge) : Bool :=
  match tryMove (g.sourceState edge) edge.piece edge.direction with
  | none => false
  | some actual => decide (SameShape actual (g.targetState edge))

theorem checkEdge_sound {g : Graph} {edge : Edge}
    (h : checkEdge g edge = true) :
    QStep (g.sourceState edge) (g.targetState edge) := by
  unfold checkEdge at h
  cases hm : tryMove (g.sourceState edge) edge.piece edge.direction with
  | none => simp [hm] at h
  | some actual =>
      simp [hm] at h
      exact ⟨edge.piece, edge.direction, actual, hm, h⟩

def checkEdges (g : Graph) : Bool := g.edges.all (checkEdge g)

theorem checkEdges_sound {g : Graph} (h : checkEdges g = true)
    (i : Nat) (hi : i < g.edges.size) :
    QStep (g.sourceState g.edges[i]) (g.targetState g.edges[i]) := by
  apply checkEdge_sound
  exact (Array.all_eq_true.mp h) i hi

/-- Does this graph contain a representative of the geometric state? -/
def Graph.containsShape (g : Graph) (state : State) : Bool :=
  g.states.any fun representative => decide (SameShape state representative)

def checkStateClosed (g : Graph) (state : State) : Bool :=
  (legalMoves state).all fun move => g.containsShape move.2.2

/-- Every legal successor of every stored representative is represented. -/
def checkClosed (g : Graph) : Bool :=
  g.states.all (checkStateClosed g)

theorem containsShape_sound {g : Graph} {state : State}
    (h : g.containsShape state = true) :
    ∃ i : Nat, ∃ hi : i < g.states.size, SameShape state g.states[i] := by
  unfold Graph.containsShape at h
  rw [Array.any_eq_true] at h
  rcases h with ⟨i, hi, hs⟩
  exact ⟨i, hi, of_decide_eq_true hs⟩

theorem checkStateClosed_sound {g : Graph} {state : State}
    (h : checkStateClosed g state = true)
    {p : Piece} {d : Direction} {next : State}
    (hm : tryMove state p d = some next) :
    ∃ i : Nat, ∃ hi : i < g.states.size, SameShape next g.states[i] := by
  have member : (p, d, next) ∈ legalMoves state := legalMoves_complete hm
  unfold checkStateClosed at h
  rw [List.all_eq_true] at h
  exact containsShape_sound (h (p, d, next) member)

theorem checkClosed_sound {g : Graph} (h : checkClosed g = true)
    (i : Nat) (hi : i < g.states.size)
    {p : Piece} {d : Direction} {next : State}
    (hm : tryMove g.states[i] p d = some next) :
    ∃ j : Nat, ∃ hj : j < g.states.size, SameShape next g.states[j] := by
  unfold checkClosed at h
  rw [Array.all_eq_true] at h
  exact checkStateClosed_sound (h i hi) hm

/-- Distances are array-aligned, root is zero, and edges change distance by at most one. -/
def checkDistances (g : Graph) : Bool :=
  g.states.size = g.distance.size &&
  g.distance.getD 0 1 = 0 &&
  g.edges.all fun edge =>
    g.distance.getD edge.target 0 ≤ g.distance.getD edge.source 0 + 1

theorem checkDistances_root {g : Graph} (h : checkDistances g = true) :
    g.distance.getD 0 1 = 0 := by
  unfold checkDistances at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.2

theorem checkDistances_edge {g : Graph} (h : checkDistances g = true)
    (i : Nat) (hi : i < g.edges.size) :
    g.distance.getD g.edges[i].target 0 ≤
      g.distance.getD g.edges[i].source 0 + 1 := by
  unfold checkDistances at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true ((Array.all_eq_true.mp h.2) i hi)

/-- A graph path carrying both quotient-step and distance certificates. -/
inductive GraphPath (g : Graph) : Nat → Nat → Type where
  | nil (node : Nat) : GraphPath g node node
  | cons {source middle target : Nat}
      (step : QStep (g.states.getD source classic) (g.states.getD middle classic))
      (distanceStep : g.distance.getD middle 0 ≤ g.distance.getD source 0 + 1)
      (tail : GraphPath g middle target) : GraphPath g source target

namespace GraphPath

def length : GraphPath g source target → Nat
  | .nil _ => 0
  | .cons _ _ tail => tail.length + 1

  theorem distance_le (path : GraphPath g source target) :
      g.distance.getD target 0 ≤ g.distance.getD source 0 + path.length := by
    induction path with
    | nil => simp [length]
    | cons _ distanceStep tail ih =>
        simp only [length]
        omega

end GraphPath

/--
An abstract quotient graph certificate.  `represents s q` says that the concrete
state `s` lies in quotient node `q`.  The two simulation fields make the
concrete transition system and quotient graph bisimilar on represented states.
Only `simulateForward` is needed for the lower-bound theorem; the reverse
field records the stronger, independently checkable quotient specification.
-/
structure QuotientLowerBoundCertificate (start : State) (bound : Nat) where
  Node : Type
  Edge : Node → Node → Prop
  represents : State → Node → Prop
  startNode : Node
  startRepresented : represents start startNode
  simulateForward : ∀ {s t : State} {q : Node},
    represents s q → Step s t → ∃ r : Node, Edge q r ∧ represents t r
  simulateBackward : ∀ {s : State} {q r : Node},
    represents s q → Edge q r → ∃ t : State, Step s t ∧ represents t r
  potential : Node → Nat
  startPotential : potential startNode = 0
  potentialStep : ∀ {q r : Node}, Edge q r → potential r ≤ potential q + 1
  goalLowerBound : ∀ {t : State} {q : Node},
    represents t q → goal t = true → bound ≤ potential q

namespace QuotientLowerBoundCertificate

/-- Lift a concrete path through quotient closure while accumulating potential. -/
theorem path_potential_le_aux
    (certificate : QuotientLowerBoundCertificate initial bound)
    {s target : State} {q : certificate.Node}
    (represented : certificate.represents s q)
    (path : Path s target) :
    ∃ r : certificate.Node,
      certificate.represents target r ∧
      certificate.potential r ≤ certificate.potential q + path.length := by
  induction path generalizing q with
  | nil => exact ⟨q, represented, by simp [Path.length]⟩
  | cons action move tail ih =>
      rcases certificate.simulateForward represented ⟨action, move⟩ with
        ⟨r, edge, nextRepresented⟩
      rcases ih nextRepresented with ⟨u, targetRepresented, potentialTail⟩
      refine ⟨u, targetRepresented, ?_⟩
      have potentialHead := certificate.potentialStep edge
      simp only [Path.length]
      omega

theorem path_potential_le
    (certificate : QuotientLowerBoundCertificate start bound)
    (path : Path start target) :
    ∃ r : certificate.Node,
      certificate.represents target r ∧
      certificate.potential r ≤ certificate.potential certificate.startNode + path.length :=
  certificate.path_potential_le_aux certificate.startRepresented path

/-- Every concrete solution is at least the certified quotient goal distance. -/
theorem solution_lower_bound
    (certificate : QuotientLowerBoundCertificate start bound)
    (solution : Solution start) : bound ≤ solution.length := by
  rcases certificate.path_potential_le solution.path with
    ⟨q, represented, potentialPath⟩
  have goalPotential := certificate.goalLowerBound represented solution.solved
  rw [certificate.startPotential] at potentialPath
  change bound ≤ solution.path.length
  exact Nat.le_trans goalPotential (by simpa using potentialPath)

end QuotientLowerBoundCertificate

/-- All goal representatives have distance at least n. -/
def checkGoalLowerBound (g : Graph) (n : Nat) : Bool :=
  (g.states.zip g.distance).all fun pair => !goal pair.1 || n ≤ pair.2

def checkGoalAt (g : Graph) (n : Nat) : Bool :=
  (g.states.zip g.distance).any fun pair => goal pair.1 && pair.2 = n


/-- Build the canonical-key set once, making closure checking near-linear. -/
def Graph.keySet (g : Graph) : Std.HashSet String :=
  g.states.foldl (fun keys state => keys.insert state.key) {}

def checkClosedFast (g : Graph) : Bool :=
  let keys := g.keySet
  g.states.all fun state =>
    (legalMoves state).all fun move => keys.contains move.2.2.key

/-- All stored representatives have distinct canonical keys. -/
def checkUniqueKeys (g : Graph) : Bool := Id.run do
  let mut keys : Std.HashSet String := {}
  for state in g.states do
    if keys.contains state.key then return false
    keys := keys.insert state.key
  return true

end Huarongdao
