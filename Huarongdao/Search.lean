import Huarongdao.Enumeration
import Huarongdao.Symmetry
import Huarongdao.ProofGame
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
  index : Std.HashMap String Nat

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
  return ⟨states, edges, distance, known⟩

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

/-- Strengthen a quotient edge with an explicit equal-shape relabeling witness. -/
def checkRelabeledEdge (g : Graph) (edge : Edge) : Bool :=
  match tryMove (g.sourceState edge) edge.piece edge.direction with
  | none => false
  | some actual => (findShapeRelabeling actual (g.targetState edge)).isSome

theorem checkRelabeledEdge_sound {g : Graph} {edge : Edge}
    (h : checkRelabeledEdge g edge = true) :
    ∃ actual σ,
      tryMove (g.sourceState edge) edge.piece edge.direction = some actual ∧
      actual = relabelState σ (g.targetState edge) := by
  unfold checkRelabeledEdge at h
  cases hm : tryMove (g.sourceState edge) edge.piece edge.direction with
  | none => simp [hm] at h
  | some actual =>
      cases hr : findShapeRelabeling actual (g.targetState edge) with
      | none => simp [hm, hr] at h
      | some σ =>
          exact ⟨actual, σ, rfl, (findShapeRelabeling_sound hr).symm⟩

def checkRelabeledEdges (g : Graph) : Bool := g.edges.all (checkRelabeledEdge g)

/-- Locate a concrete state as an exact relabeling of its indexed representative. -/
def Graph.findRepresentation (g : Graph) (state : State) : Option (Nat × PieceRelabeling) := do
  let i ← g.index.get? state.key
  if i < g.states.size then
    let σ ← findShapeRelabeling state (g.states.getD i classic)
    return (i, σ)
  else
    none

theorem Graph.findRepresentation_sound {g : Graph} {state : State}
    {i : Nat} {σ : PieceRelabeling}
    (h : g.findRepresentation state = some (i, σ)) :
    i < g.states.size ∧ state = relabelState σ (g.states.getD i classic) := by
  unfold Graph.findRepresentation at h
  cases hi : g.index.get? state.key with
  | none =>
      rw [hi] at h
      simp at h
  | some candidate =>
      rw [hi] at h
      by_cases bound : candidate < g.states.size
      · simp [bound] at h
        cases hr : findShapeRelabeling state g.states[candidate] with
        | none =>
            simp [hr] at h
        | some relabeling =>
            rw [hr] at h
            have pairEq : (candidate, relabeling) = (i, σ) := Option.some.inj h
            have indexEq : candidate = i := congrArg Prod.fst pairEq
            have relabelEq : relabeling = σ := congrArg Prod.snd pairEq
            subst i
            subst σ
            exact ⟨bound, by simpa [bound] using (findShapeRelabeling_sound hr).symm⟩
      · simp [bound] at h

def checkTransitionFrom (g : Graph) (i : Nat) : Bool :=
  (legalMoves (g.states.getD i classic)).all fun move =>
    match g.findRepresentation move.2.2 with
    | none => false
    | some (j, _) => g.distance.getD j 0 ≤ g.distance.getD i 0 + 1

/-- Every legal move from every stored representative has a represented target
    whose potential grows by at most one. -/
def checkRelabeledClosed (g : Graph) : Bool :=
  (List.range g.states.size).all (checkTransitionFrom g)

theorem checkRelabeledClosed_sound {g : Graph} (h : checkRelabeledClosed g = true)
    (i : Nat) (hi : i < g.states.size)
    {p : Piece} {d : Direction} {next : State}
    (hm : tryMove (g.states.getD i classic) p d = some next) :
    ∃ j σ, j < g.states.size ∧
      next = relabelState σ (g.states.getD j classic) ∧
      g.distance.getD j 0 ≤ g.distance.getD i 0 + 1 := by
  have member : (p, d, next) ∈ legalMoves (g.states.getD i classic) := legalMoves_complete hm
  unfold checkRelabeledClosed at h
  rw [List.all_eq_true] at h
  have checked := h i (List.mem_range.mpr hi)
  unfold checkTransitionFrom at checked
  rw [List.all_eq_true] at checked
  have checked := checked (p, d, next) member
  cases hr : g.findRepresentation next with
  | none => simp [hr] at checked
  | some representation =>
      rcases representation with ⟨j, σ⟩
      rw [hr] at checked
      have sound := Graph.findRepresentation_sound hr
      exact ⟨j, σ, sound.1, sound.2, of_decide_eq_true checked⟩

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

/-- Execute a player's action list through the represented quotient nodes. -/
theorem runMoves_potential_le_aux
    (certificate : QuotientLowerBoundCertificate initial bound)
    {s target : State} {q : certificate.Node} {actions : List Action}
    (represented : certificate.represents s q)
    (executed : runMoves s actions = some target) :
    ∃ r : certificate.Node,
      certificate.represents target r ∧
      certificate.potential r ≤ certificate.potential q + actions.length := by
  induction actions generalizing s q with
  | nil =>
      simp [runMoves] at executed
      subst target
      exact ⟨q, represented, by simp⟩
  | cons action rest ih =>
      cases hm : tryMove s action.piece action.direction with
      | none => simp [runMoves, hm] at executed
      | some next =>
          simp [runMoves, hm] at executed
          rcases certificate.simulateForward represented ⟨action, hm⟩ with
            ⟨r, edge, nextRepresented⟩
          rcases ih nextRepresented executed with
            ⟨u, targetRepresented, potentialTail⟩
          refine ⟨u, targetRepresented, ?_⟩
          have potentialHead := certificate.potentialStep edge
          simp only [List.length_cons]
          omega

/-- The quotient certificate applies directly to executable player input. -/
theorem play_lower_bound
    (certificate : QuotientLowerBoundCertificate start bound)
    (play : CertifiedPlay start) : bound ≤ play.length := by
  rcases certificate.runMoves_potential_le_aux certificate.startRepresented
      play.executed with ⟨q, represented, potentialPath⟩
  have goalPotential := certificate.goalLowerBound represented play.solved
  rw [certificate.startPotential] at potentialPath
  change bound ≤ play.actions.length
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

/-- A concrete state is represented by a graph node up to equal-shape labels. -/
def Graph.Represents (g : Graph) (s : State) (q : Fin g.states.size) : Prop :=
  ∃ σ : PieceRelabeling,
    ObservationalEq s (relabelState σ (g.states.getD q classic))

/-- A checked quotient transition, including the local distance inequality. -/
def Graph.CertificateEdge (g : Graph)
    (q r : Fin g.states.size) : Prop :=
  ∃ p d next σ,
    tryMove (g.states.getD q classic) p d = some next ∧
    next = relabelState σ (g.states.getD r classic) ∧
    g.distance.getD r 0 ≤ g.distance.getD q 0 + 1

def checkStartRepresentation (g : Graph) (start : State) : Bool :=
  (findShapeRelabeling start (g.states.getD 0 classic)).isSome

theorem findShapeRelabeling_isSome_sound {source representative : State}
    (h : (findShapeRelabeling source representative).isSome = true) :
    ∃ σ, source = relabelState σ representative := by
  cases hr : findShapeRelabeling source representative with
  | none => simp [hr] at h
  | some σ => exact ⟨σ, (findShapeRelabeling_sound hr).symm⟩

theorem checkStartRepresentation_sound {g : Graph} {start : State}
    (h : checkStartRepresentation g start = true) :
    ∃ σ, start = relabelState σ (g.states.getD 0 classic) := by
  apply findShapeRelabeling_isSome_sound
  exact h

/-- Check the lower-bound condition at every stored goal representative. -/
def checkIndexedGoalLowerBound (g : Graph) (bound : Nat) : Bool :=
  (List.range g.states.size).all fun i =>
    !goal (g.states.getD i classic) || bound ≤ g.distance.getD i 0

theorem checkIndexedGoalLowerBound_sound {g : Graph} {bound : Nat}
    (h : checkIndexedGoalLowerBound g bound = true)
    (i : Nat) (hi : i < g.states.size)
    (hgoal : goal (g.states.getD i classic) = true) :
    bound ≤ g.distance.getD i 0 := by
  unfold checkIndexedGoalLowerBound at h
  rw [List.all_eq_true] at h
  have checked := h i (List.mem_range.mpr hi)
  rw [Bool.or_eq_true] at checked
  rcases checked with goalNot | distanceBound
  · rw [hgoal] at goalNot
    contradiction
  · exact of_decide_eq_true distanceBound

/-- All executable conditions needed to construct the quotient certificate. -/
def checkQuotientLowerBound (g : Graph) (start : State) (bound : Nat) : Bool :=
  decide (0 < g.states.size) &&
  checkStartRepresentation g start &&
  decide (g.distance.getD 0 0 = 0) &&
  checkRelabeledClosed g &&
  checkIndexedGoalLowerBound g bound

/-- Turn successful executable graph checks into a proof-carrying certificate. -/
def Graph.quotientLowerBoundCertificate (g : Graph) (start : State) (bound : Nat)
    (nonempty : 0 < g.states.size)
    (startChecked : checkStartRepresentation g start = true)
    (rootDistance : g.distance.getD 0 0 = 0)
    (closed : checkRelabeledClosed g = true)
    (goals : checkIndexedGoalLowerBound g bound = true) :
    QuotientLowerBoundCertificate start bound where
  Node := Fin g.states.size
  Edge := g.CertificateEdge
  represents := g.Represents
  startNode := ⟨0, nonempty⟩
  startRepresented := by
    rcases checkStartRepresentation_sound startChecked with ⟨σ, hs⟩
    exact ⟨σ, by rw [hs]; intro p; rfl⟩
  simulateForward := by
    intro s t q represented step
    rcases represented with ⟨α, hs⟩
    rcases step with ⟨action, hm⟩
    have hmRelabeled :
        tryMove (relabelState α (g.states.getD q classic))
          action.piece action.direction = some t := by
      have sameMove := observational_tryMove hs action.piece action.direction
      rw [hm] at sameMove
      exact sameMove.symm
    rcases tryMove_unrelabel hmRelabeled with ⟨actual, hactual, ht⟩
    rcases checkRelabeledClosed_sound closed q q.isLt hactual with
      ⟨j, β, hj, representedNext, distanceNext⟩
    let r : Fin g.states.size := ⟨j, hj⟩
    refine ⟨r, ?_, ?_⟩
    · exact ⟨α.inverse action.piece, action.direction, actual, β,
        hactual, representedNext, distanceNext⟩
    · refine ⟨α.comp β, ?_⟩
      rw [ht, representedNext, relabel_comp]
      intro p
      rfl
  simulateBackward := by
    intro s q r represented edge
    rcases represented with ⟨α, hs⟩
    rcases edge with ⟨p, d, next, β, hm, representedNext, _⟩
    let t := relabelState α next
    have mappedMove :
        tryMove (relabelState α (g.states.getD q classic)) (α.forward p) d =
          some t := by
      rw [tryMove_relabel, hm]
      rfl
    have concreteMove : tryMove s (α.forward p) d = some t := by
      rw [observational_tryMove hs]
      exact mappedMove
    refine ⟨t, ⟨⟨α.forward p, d⟩, concreteMove⟩, ?_⟩
    refine ⟨α.comp β, ?_⟩
    change ObservationalEq (relabelState α next)
      (relabelState (α.comp β) (g.states.getD r classic))
    rw [representedNext, relabel_comp]
    intro piece
    rfl
  potential := fun q => g.distance.getD q 0
  startPotential := rootDistance
  potentialStep := by
    intro q r edge
    rcases edge with ⟨_, _, _, _, _, _, distanceStep⟩
    exact distanceStep
  goalLowerBound := by
    intro t q represented hgoal
    rcases represented with ⟨α, ht⟩
    apply checkIndexedGoalLowerBound_sound goals q q.isLt
    calc
      goal (g.states.getD q classic) =
          goal (relabelState α (g.states.getD q classic)) :=
        (goal_relabel α _).symm
      _ = goal t := (observational_goal ht).symm
      _ = true := hgoal

theorem checkQuotientLowerBound_sound {g : Graph} {start : State} {bound : Nat}
    (h : checkQuotientLowerBound g start bound = true) :
    Nonempty (QuotientLowerBoundCertificate start bound) := by
  unfold checkQuotientLowerBound at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hsize, hstart⟩, hroot⟩, hclosed⟩, hgoals⟩
  exact ⟨g.quotientLowerBoundCertificate start bound
    (of_decide_eq_true hsize) hstart (of_decide_eq_true hroot) hclosed hgoals⟩

end Huarongdao
