import Huarongdao.Enumeration
import Huarongdao.Relabeling
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
  | some actual =>
      (findShapeRelabeling actual (g.targetState edge)).isSome

theorem checkRelabeledEdge_sound {g : Graph} {edge : Edge}
    (h : checkRelabeledEdge g edge = true) :
    ∃ actual relabeling,
      tryMove (g.sourceState edge) edge.piece edge.direction =
        some actual ∧
      actual = relabelState relabeling (g.targetState edge) := by
  unfold checkRelabeledEdge at h
  cases executed :
      tryMove (g.sourceState edge) edge.piece edge.direction with
  | none =>
      simp [executed] at h
  | some actual =>
      cases found :
          findShapeRelabeling actual (g.targetState edge) with
      | none =>
          simp [executed, found] at h
      | some relabeling =>
          exact
            ⟨actual, relabeling, rfl,
              (findShapeRelabeling_sound found).symm⟩

def checkRelabeledEdges (g : Graph) : Bool :=
  g.edges.all (checkRelabeledEdge g)

/-- Locate a concrete state as an exact relabeling of its indexed representative. -/
def Graph.findRepresentation (g : Graph) (state : State) :
    Option (Nat × PieceRelabeling) := do
  let index ← g.index.get? state.key
  if index < g.states.size then
    let relabeling ←
      findShapeRelabeling state (g.states.getD index classic)
    return (index, relabeling)
  else
    none

theorem Graph.findRepresentation_sound
    {g : Graph} {state : State} {index : Nat}
    {relabeling : PieceRelabeling}
    (h : g.findRepresentation state = some (index, relabeling)) :
    index < g.states.size ∧
      state = relabelState relabeling
        (g.states.getD index classic) := by
  unfold Graph.findRepresentation at h
  cases indexed : g.index.get? state.key with
  | none =>
      rw [indexed] at h
      simp at h
  | some candidate =>
      rw [indexed] at h
      by_cases bound : candidate < g.states.size
      · simp [bound] at h
        cases found :
            findShapeRelabeling state g.states[candidate] with
        | none =>
            simp [found] at h
        | some candidateRelabeling =>
            rw [found] at h
            have pairEq :
                (candidate, candidateRelabeling) =
                  (index, relabeling) :=
              Option.some.inj h
            have indexEq : candidate = index :=
              congrArg Prod.fst pairEq
            have relabelingEq :
                candidateRelabeling = relabeling :=
              congrArg Prod.snd pairEq
            subst index
            subst relabeling
            exact
              ⟨bound, by
                simpa [bound] using
                  (findShapeRelabeling_sound found).symm⟩
      · simp [bound] at h

def checkTransitionFrom (g : Graph) (index : Nat) : Bool :=
  (legalMoves (g.states.getD index classic)).all fun move =>
    match g.findRepresentation move.2.2 with
    | none => false
    | some (target, _) =>
        g.distance.getD target 0 ≤
          g.distance.getD index 0 + 1

/-- Every legal move from every stored representative has a represented target
    whose potential grows by at most one. -/
def checkRelabeledClosed (g : Graph) : Bool :=
  (List.range g.states.size).all (checkTransitionFrom g)

theorem checkRelabeledClosed_sound {g : Graph}
    (h : checkRelabeledClosed g = true)
    (index : Nat) (indexLt : index < g.states.size)
    {piece : Piece} {direction : Direction} {next : State}
    (executed :
      tryMove (g.states.getD index classic) piece direction =
        some next) :
    ∃ target relabeling,
      target < g.states.size ∧
      next = relabelState relabeling
        (g.states.getD target classic) ∧
      g.distance.getD target 0 ≤
        g.distance.getD index 0 + 1 := by
  have member :
      (piece, direction, next) ∈
        legalMoves (g.states.getD index classic) :=
    legalMoves_complete executed
  unfold checkRelabeledClosed at h
  rw [List.all_eq_true] at h
  have checked := h index (List.mem_range.mpr indexLt)
  unfold checkTransitionFrom at checked
  rw [List.all_eq_true] at checked
  have checked := checked (piece, direction, next) member
  cases represented : g.findRepresentation next with
  | none =>
      simp [represented] at checked
  | some representation =>
      rcases representation with ⟨target, relabeling⟩
      rw [represented] at checked
      have sound := Graph.findRepresentation_sound represented
      exact
        ⟨target, relabeling, sound.1, sound.2,
          of_decide_eq_true checked⟩

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
    {source target : State} {node : certificate.Node}
    {actions : List Action}
    (represented : certificate.represents source node)
    (executed : runMoves source actions = some target) :
    ∃ targetNode : certificate.Node,
      certificate.represents target targetNode ∧
      certificate.potential targetNode ≤
        certificate.potential node + actions.length := by
  induction actions generalizing source node with
  | nil =>
      simp [runMoves] at executed
      subst target
      exact ⟨node, represented, by simp⟩
  | cons action rest inductionHypothesis =>
      cases moved :
          tryMove source action.piece action.direction with
      | none =>
          simp [runMoves, moved] at executed
      | some next =>
          simp [runMoves, moved] at executed
          rcases certificate.simulateForward represented
              ⟨action, moved⟩ with
            ⟨nextNode, edge, nextRepresented⟩
          rcases inductionHypothesis nextRepresented executed with
            ⟨targetNode, targetRepresented, tailBound⟩
          refine ⟨targetNode, targetRepresented, ?_⟩
          have headBound := certificate.potentialStep edge
          simp only [List.length_cons]
          omega

/-- The quotient certificate applies directly to executable player input. -/
theorem play_lower_bound
    (certificate : QuotientLowerBoundCertificate start bound)
    (play : CertifiedPlay start) :
    bound ≤ play.length := by
  rcases certificate.runMoves_potential_le_aux
      certificate.startRepresented play.executed with
    ⟨targetNode, represented, pathBound⟩
  have goalBound :=
    certificate.goalLowerBound represented play.solved
  rw [certificate.startPotential] at pathBound
  change bound ≤ play.actions.length
  exact Nat.le_trans goalBound (by simpa using pathBound)

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
def Graph.Represents (g : Graph)
    (state : State) (node : Fin g.states.size) : Prop :=
  ∃ relabeling : PieceRelabeling,
    ObservationalEq state
      (relabelState relabeling
        (g.states.getD node classic))

/-- A checked quotient transition, including the local distance inequality. -/
def Graph.CertificateEdge (g : Graph)
    (source target : Fin g.states.size) : Prop :=
  ∃ piece direction next relabeling,
    tryMove (g.states.getD source classic) piece direction =
      some next ∧
    next = relabelState relabeling
      (g.states.getD target classic) ∧
    g.distance.getD target 0 ≤
      g.distance.getD source 0 + 1

def checkStartRepresentation
    (g : Graph) (start : State) : Bool :=
  (findShapeRelabeling start
    (g.states.getD 0 classic)).isSome

theorem findShapeRelabeling_isSome_sound
    {source representative : State}
    (h :
      (findShapeRelabeling source representative).isSome = true) :
    ∃ relabeling,
      source = relabelState relabeling representative := by
  cases found :
      findShapeRelabeling source representative with
  | none =>
      simp [found] at h
  | some relabeling =>
      exact
        ⟨relabeling,
          (findShapeRelabeling_sound found).symm⟩

theorem checkStartRepresentation_sound
    {g : Graph} {start : State}
    (h : checkStartRepresentation g start = true) :
    ∃ relabeling,
      start = relabelState relabeling
        (g.states.getD 0 classic) := by
  apply findShapeRelabeling_isSome_sound
  exact h

/-- Check the lower-bound condition at every stored goal representative. -/
def checkIndexedGoalLowerBound
    (g : Graph) (bound : Nat) : Bool :=
  (List.range g.states.size).all fun index =>
    !goal (g.states.getD index classic) ||
      bound ≤ g.distance.getD index 0

theorem checkIndexedGoalLowerBound_sound
    {g : Graph} {bound : Nat}
    (h : checkIndexedGoalLowerBound g bound = true)
    (index : Nat) (indexLt : index < g.states.size)
    (isGoal : goal (g.states.getD index classic) = true) :
    bound ≤ g.distance.getD index 0 := by
  unfold checkIndexedGoalLowerBound at h
  rw [List.all_eq_true] at h
  have checked := h index (List.mem_range.mpr indexLt)
  rw [Bool.or_eq_true] at checked
  rcases checked with notGoal | distanceBound
  · rw [isGoal] at notGoal
    contradiction
  · exact of_decide_eq_true distanceBound

/-- All executable conditions needed to construct the quotient certificate. -/
def checkQuotientLowerBound
    (g : Graph) (start : State) (bound : Nat) : Bool :=
  decide (0 < g.states.size) &&
  checkStartRepresentation g start &&
  decide (g.distance.getD 0 0 = 0) &&
  checkRelabeledClosed g &&
  checkIndexedGoalLowerBound g bound

/-- Turn successful executable graph checks into a proof-carrying certificate. -/
def Graph.quotientLowerBoundCertificate
    (g : Graph) (start : State) (bound : Nat)
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
    rcases checkStartRepresentation_sound startChecked with
      ⟨relabeling, startEq⟩
    exact
      ⟨relabeling, by
        rw [startEq]
        intro piece
        rfl⟩
  simulateForward := by
    intro source target node represented step
    rcases represented with ⟨sourceRelabeling, sourceEq⟩
    rcases step with ⟨action, executed⟩
    have relabeledMove :
        tryMove
            (relabelState sourceRelabeling
              (g.states.getD node classic))
            action.piece action.direction =
          some target := by
      have sameMove :=
        observational_tryMove sourceEq
          action.piece action.direction
      rw [executed] at sameMove
      exact sameMove.symm
    rcases tryMove_unrelabel relabeledMove with
      ⟨actual, representativeMove, targetEq⟩
    rcases checkRelabeledClosed_sound
        closed node node.isLt representativeMove with
      ⟨targetIndex, targetRelabeling, targetLt,
        representedNext, distanceNext⟩
    let targetNode : Fin g.states.size :=
      ⟨targetIndex, targetLt⟩
    refine ⟨targetNode, ?_, ?_⟩
    · exact
        ⟨sourceRelabeling.inverse action.piece,
          action.direction, actual, targetRelabeling,
          representativeMove, representedNext,
          distanceNext⟩
    · refine
        ⟨sourceRelabeling.comp targetRelabeling, ?_⟩
      rw [targetEq, representedNext, relabel_comp]
      intro piece
      rfl
  simulateBackward := by
    intro source sourceNode targetNode represented edge
    rcases represented with ⟨sourceRelabeling, sourceEq⟩
    rcases edge with
      ⟨piece, direction, next, targetRelabeling,
        executed, representedNext, _⟩
    let target := relabelState sourceRelabeling next
    have mappedMove :
        tryMove
            (relabelState sourceRelabeling
              (g.states.getD sourceNode classic))
            (sourceRelabeling.forward piece) direction =
          some target := by
      rw [tryMove_relabel, executed]
      rfl
    have concreteMove :
        tryMove source
            (sourceRelabeling.forward piece) direction =
          some target := by
      rw [observational_tryMove sourceEq]
      exact mappedMove
    refine
      ⟨target,
        ⟨⟨sourceRelabeling.forward piece, direction⟩,
          concreteMove⟩,
        ?_⟩
    refine
      ⟨sourceRelabeling.comp targetRelabeling, ?_⟩
    change
      ObservationalEq
        (relabelState sourceRelabeling next)
        (relabelState
          (sourceRelabeling.comp targetRelabeling)
          (g.states.getD targetNode classic))
    rw [representedNext, relabel_comp]
    intro candidate
    rfl
  potential := fun node => g.distance.getD node 0
  startPotential := rootDistance
  potentialStep := by
    intro source target edge
    rcases edge with
      ⟨_, _, _, _, _, _, distanceStep⟩
    exact distanceStep
  goalLowerBound := by
    intro target node represented isGoal
    rcases represented with ⟨relabeling, targetEq⟩
    apply checkIndexedGoalLowerBound_sound
      goals node node.isLt
    calc
      goal (g.states.getD node classic) =
          goal
            (relabelState relabeling
              (g.states.getD node classic)) :=
        (goal_relabel relabeling _).symm
      _ = goal target :=
        (observational_goal targetEq).symm
      _ = true := isGoal

theorem checkQuotientLowerBound_sound
    {g : Graph} {start : State} {bound : Nat}
    (h : checkQuotientLowerBound g start bound = true) :
    Nonempty (QuotientLowerBoundCertificate start bound) := by
  unfold checkQuotientLowerBound at h
  simp only [Bool.and_eq_true] at h
  rcases h with
    ⟨⟨⟨⟨sizeChecked, startChecked⟩,
      rootChecked⟩, closed⟩, goals⟩
  exact
    ⟨g.quotientLowerBoundCertificate start bound
      (of_decide_eq_true sizeChecked)
      startChecked
      (of_decide_eq_true rootChecked)
      closed goals⟩

end Huarongdao
