import Huarongdao.MirrorQuotient
import Huarongdao.Search

namespace Huarongdao

/-!
This module makes the horizontal-mirror quotient executable.  The semantic
quotient is still `MirrorShapeState`; this file supplies a finite
representative presentation whose nodes are raw states indexed by `mirrorKey`.
-/

/-- The canonical key for the two-stage equal-shape/mirror quotient. -/
def mirrorKey (state : State) : String :=
  let own := state.key
  let reflected := (mirrorState state).key
  if own ≤ reflected then own else reflected

/-- Raw-state form of equality in the equal-shape/mirror quotient. -/
def MirrorRepresentativeEq (source target : State) : Prop :=
  SameShape source target ∨ SameShape (mirrorState source) target

instance (source target : State) :
    Decidable (MirrorRepresentativeEq source target) := by
  unfold MirrorRepresentativeEq
  infer_instance

/-- A finite graph whose states are indexed directly by mirror classes. -/
def enumerateMirror : Graph :=
  enumerateByKey classic mirrorKey

/-- An indexed representative for a state in a mirror-keyed graph. -/
def Graph.findMirrorRepresentation (graph : Graph) (state : State) :
    Option Nat := do
  let index ← graph.index.get? (mirrorKey state)
  if index < graph.states.size then
    if decide
        (MirrorRepresentativeEq state
          (graph.states.getD index classic)) then
      some index
    else
      none
  else
    none

theorem Graph.findMirrorRepresentation_sound
    {graph : Graph} {state : State} {index : Nat}
    (checked :
      graph.findMirrorRepresentation state = some index) :
    index < graph.states.size ∧
      MirrorRepresentativeEq state
        (graph.states.getD index classic) := by
  unfold Graph.findMirrorRepresentation at checked
  cases indexed : graph.index.get? (mirrorKey state) with
  | none =>
      rw [indexed] at checked
      simp at checked
  | some candidate =>
      rw [indexed] at checked
      by_cases bound : candidate < graph.states.size
      · by_cases equivalent :
            MirrorRepresentativeEq state
              (graph.states.getD candidate classic)
        · have candidateEq : candidate = index := by
            have checked' :
                MirrorRepresentativeEq state
                    (graph.states.getD candidate classic) ∧
                  candidate = index := by
              simpa [bound, equivalent] using checked
            exact checked'.2
          subst index
          exact ⟨bound, equivalent⟩
        · simp [bound] at checked
          have equivalent' :
              MirrorRepresentativeEq state
                (graph.states.getD candidate classic) := by
            simpa [bound] using checked.1
          exact False.elim (equivalent equivalent')
      · simp [bound] at checked

/-- Check one edge against the mirror quotient relation. -/
def checkMirrorEdge (graph : Graph) (edge : Edge) : Bool :=
  match tryMove (graph.sourceState edge) edge.piece edge.direction with
  | none => false
  | some actual =>
      decide
        (MirrorRepresentativeEq actual (graph.targetState edge))

theorem checkMirrorEdge_sound {graph : Graph} {edge : Edge}
    (checked : checkMirrorEdge graph edge = true) :
    ∃ actual,
      tryMove (graph.sourceState edge) edge.piece edge.direction =
        some actual ∧
      MirrorRepresentativeEq actual (graph.targetState edge) := by
  unfold checkMirrorEdge at checked
  cases executed :
      tryMove (graph.sourceState edge) edge.piece edge.direction with
  | none =>
      simp [executed] at checked
  | some actual =>
      simp [executed] at checked
      exact ⟨actual, rfl, checked⟩

def checkMirrorEdges (graph : Graph) : Bool :=
  graph.edges.all (checkMirrorEdge graph)

theorem checkMirrorEdges_sound {graph : Graph}
    (checked : checkMirrorEdges graph = true)
    (index : Nat) (indexLt : index < graph.edges.size) :
    ∃ actual,
      tryMove (graph.sourceState graph.edges[index])
          graph.edges[index].piece graph.edges[index].direction =
        some actual ∧
      MirrorRepresentativeEq actual
        (graph.targetState graph.edges[index]) := by
  exact checkMirrorEdge_sound
    ((Array.all_eq_true.mp checked) index indexLt)

def checkMirrorEdgeEndpoint (graph : Graph) (edge : Edge) : Bool :=
  edge.source < graph.states.size && edge.target < graph.states.size

def checkMirrorStoredMove
    (graph : Graph) (source target : Nat)
    (move : Piece × Direction × State) : Bool :=
  graph.edges.any fun edge =>
    decide
      (edge.source = source ∧
        edge.target = target ∧
        edge.piece = move.1 ∧
        edge.direction = move.2.1 ∧
        checkMirrorEdge graph edge = true ∧
        graph.distance.getD target 0 ≤
          graph.distance.getD source 0 + 1)

def checkMirrorTransitionEdges (graph : Graph) (index : Nat) : Bool :=
  (legalMoves (graph.states.getD index classic)).all fun move =>
    match graph.findMirrorRepresentation move.2.2 with
    | none => false
    | some target => checkMirrorStoredMove graph index target move

/-!
The complete edge-integrity check has both directions:

* every stored edge is a valid mirror-quotient move; and
* every legal move from every stored representative has a matching stored edge.

The endpoint check prevents the fallback values used by `getD` from masking a
malformed edge index.
-/
def checkMirrorEdgesComplete (graph : Graph) : Bool :=
  graph.edges.all (checkMirrorEdgeEndpoint graph) &&
    checkMirrorEdges graph &&
    (List.range graph.states.size).all (checkMirrorTransitionEdges graph)

theorem checkMirrorEdgesComplete_edge_sound
    {graph : Graph}
    (checked : checkMirrorEdgesComplete graph = true)
    (index : Nat) (indexLt : index < graph.edges.size) :
    ∃ actual,
      tryMove (graph.sourceState graph.edges[index])
          graph.edges[index].piece graph.edges[index].direction =
        some actual ∧
      MirrorRepresentativeEq actual
        (graph.targetState graph.edges[index]) := by
  unfold checkMirrorEdgesComplete at checked
  rw [Bool.and_eq_true, Bool.and_eq_true] at checked
  exact checkMirrorEdge_sound
    ((Array.all_eq_true.mp checked.1.2) index indexLt)

theorem checkMirrorStoredMove_sound
    {graph : Graph} {source target : Nat}
    {move : Piece × Direction × State}
    (checked : checkMirrorStoredMove graph source target move = true) :
    ∃ edge,
      edge ∈ graph.edges.toList ∧
      edge.source = source ∧
      edge.target = target ∧
      edge.piece = move.1 ∧
      edge.direction = move.2.1 ∧
      checkMirrorEdge graph edge = true ∧
      graph.distance.getD target 0 ≤
        graph.distance.getD source 0 + 1 := by
  unfold checkMirrorStoredMove at checked
  rw [Array.any_eq_true] at checked
  rcases checked with ⟨edgeIndex, edgeIndexLt, edgeChecked⟩
  let edge : Edge := graph.edges[edgeIndex]
  have edgeMem : edge ∈ graph.edges.toList := by
    simp [edge]
  have edgeChecked' :
      decide
          (edge.source = source ∧
            edge.target = target ∧
            edge.piece = move.1 ∧
            edge.direction = move.2.1 ∧
            checkMirrorEdge graph edge = true ∧
            graph.distance.getD target 0 ≤
              graph.distance.getD source 0 + 1) = true := by
    simpa [edge] using edgeChecked
  rcases of_decide_eq_true edgeChecked' with
    ⟨sourceEq, targetEq, pieceEq, directionEq, edgeChecked,
      distanceStep⟩
  exact ⟨edge, edgeMem, sourceEq, targetEq, pieceEq, directionEq,
    edgeChecked, distanceStep⟩

theorem checkMirrorTransitionEdges_sound
    {graph : Graph} {index : Nat}
    (checked : checkMirrorTransitionEdges graph index = true)
    (_indexLt : index < graph.states.size)
    {piece : Piece} {direction : Direction} {next : State}
    (executed :
      tryMove (graph.states.getD index classic) piece direction =
        some next) :
    ∃ target edge,
      target < graph.states.size ∧
      MirrorRepresentativeEq next
        (graph.states.getD target classic) ∧
      edge ∈ graph.edges.toList ∧
      edge.source = index ∧
      edge.target = target ∧
      edge.piece = piece ∧
      edge.direction = direction ∧
      checkMirrorEdge graph edge = true ∧
      graph.distance.getD target 0 ≤
        graph.distance.getD index 0 + 1 := by
  have member :
      (piece, direction, next) ∈
        legalMoves (graph.states.getD index classic) :=
    legalMoves_complete executed
  unfold checkMirrorTransitionEdges at checked
  rw [List.all_eq_true] at checked
  have moveChecked := checked (piece, direction, next) member
  cases found : graph.findMirrorRepresentation next with
  | none =>
      simp [found] at moveChecked
  | some target =>
      have targetSound := Graph.findMirrorRepresentation_sound found
      simp only [found] at moveChecked
      rcases checkMirrorStoredMove_sound moveChecked with
        ⟨edge, edgeMem, sourceEq, targetEq, pieceEq, directionEq,
          edgeChecked, distanceStep⟩
      exact ⟨target, edge, targetSound.1, targetSound.2, edgeMem,
        sourceEq, targetEq, pieceEq, directionEq, edgeChecked,
        distanceStep⟩

theorem checkMirrorEdgesComplete_sound
    {graph : Graph}
    (checked : checkMirrorEdgesComplete graph = true)
    (index : Nat) (indexLt : index < graph.states.size)
    {piece : Piece} {direction : Direction} {next : State}
    (executed :
      tryMove (graph.states.getD index classic) piece direction =
        some next) :
    ∃ target edge,
      target < graph.states.size ∧
      MirrorRepresentativeEq next
        (graph.states.getD target classic) ∧
      edge ∈ graph.edges.toList ∧
      edge.source = index ∧
      edge.target = target ∧
      edge.piece = piece ∧
      edge.direction = direction ∧
      checkMirrorEdge graph edge = true ∧
      graph.distance.getD target 0 ≤
        graph.distance.getD index 0 + 1 := by
  unfold checkMirrorEdgesComplete at checked
  rw [Bool.and_eq_true] at checked
  exact checkMirrorTransitionEdges_sound
    ((List.all_eq_true.mp checked.2) index (List.mem_range.mpr indexLt))
    indexLt executed

def checkMirrorValidStates (graph : Graph) : Bool :=
  graph.states.all valid

theorem checkMirrorValidStates_sound {graph : Graph}
    (checked : checkMirrorValidStates graph = true)
    (index : Nat) (indexLt : index < graph.states.size) :
    ValidState (graph.states[index]) := by
  unfold checkMirrorValidStates at checked
  exact (Array.all_eq_true.mp checked) index indexLt

/-- Every legal successor of every mirror representative is indexed. -/
def checkMirrorTransitionFrom (graph : Graph) (index : Nat) : Bool :=
  (legalMoves (graph.states.getD index classic)).all fun move =>
    match graph.findMirrorRepresentation move.2.2 with
    | none => false
    | some target =>
        target < graph.states.size &&
        decide
          (graph.distance.getD target 0 ≤
            graph.distance.getD index 0 + 1)

def checkMirrorClosed (graph : Graph) : Bool :=
  (List.range graph.states.size).all (checkMirrorTransitionFrom graph)

theorem checkMirrorClosed_sound {graph : Graph}
    (checked : checkMirrorClosed graph = true)
    (index : Nat) (indexLt : index < graph.states.size)
    {piece : Piece} {direction : Direction} {next : State}
    (executed :
      tryMove (graph.states.getD index classic) piece direction =
        some next) :
    ∃ target,
      target < graph.states.size ∧
      MirrorRepresentativeEq next
        (graph.states.getD target classic) ∧
      graph.distance.getD target 0 ≤
        graph.distance.getD index 0 + 1 := by
  have member :
      (piece, direction, next) ∈
        legalMoves (graph.states.getD index classic) :=
    legalMoves_complete executed
  unfold checkMirrorClosed at checked
  rw [List.all_eq_true] at checked
  have stateChecked := checked index (List.mem_range.mpr indexLt)
  unfold checkMirrorTransitionFrom at stateChecked
  rw [List.all_eq_true] at stateChecked
  have moveChecked := stateChecked (piece, direction, next) member
  cases found : graph.findMirrorRepresentation next with
  | none =>
      simp [found] at moveChecked
  | some target =>
      rw [found] at moveChecked
      simp only [Bool.and_eq_true] at moveChecked
      have sound := Graph.findMirrorRepresentation_sound found
      exact ⟨target, sound.1, sound.2,
        of_decide_eq_true moveChecked.2⟩

def checkMirrorStartRepresentation (graph : Graph) (start : State) : Bool :=
  decide (0 < graph.states.size) &&
  decide (valid start = true) &&
  decide
    (MirrorRepresentativeEq start
      (graph.states.getD 0 classic))

theorem checkMirrorStartRepresentation_sound
    {graph : Graph} {start : State}
    (checked : checkMirrorStartRepresentation graph start = true) :
    ValidState start ∧
      0 < graph.states.size ∧
      MirrorRepresentativeEq start
        (graph.states.getD 0 classic) := by
  unfold checkMirrorStartRepresentation at checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with ⟨⟨sizeChecked, validChecked⟩, mirrorChecked⟩
  have startValid : ValidState start := by
    change valid start = true
    exact of_decide_eq_true validChecked
  have sizePositive : 0 < graph.states.size :=
    of_decide_eq_true sizeChecked
  have startEquivalent :
      MirrorRepresentativeEq start
        (graph.states.getD 0 classic) :=
    of_decide_eq_true mirrorChecked
  exact ⟨startValid, sizePositive, startEquivalent⟩

def checkMirrorGoalLowerBound (graph : Graph) (bound : Nat) : Bool :=
  (List.range graph.states.size).all fun index =>
    !goal (graph.states.getD index classic) ||
      bound ≤ graph.distance.getD index 0

theorem checkMirrorGoalLowerBound_sound
    {graph : Graph} {bound : Nat}
    (checked : checkMirrorGoalLowerBound graph bound = true)
    (index : Nat) (indexLt : index < graph.states.size)
    (isGoal : goal (graph.states.getD index classic) = true) :
    bound ≤ graph.distance.getD index 0 := by
  unfold checkMirrorGoalLowerBound at checked
  rw [List.all_eq_true] at checked
  have checked := checked index (List.mem_range.mpr indexLt)
  rw [Bool.or_eq_true] at checked
  rcases checked with notGoal | distanceBound
  · rw [isGoal] at notGoal
    contradiction
  · exact of_decide_eq_true distanceBound

theorem mirrorRepresentativeEq_refl (state : State) :
    MirrorRepresentativeEq state state :=
  Or.inl (sameShape_refl state)

theorem mirrorRepresentativeEq_symm
    {source target : State}
    (sourceValid : ValidState source)
    (_targetValid : ValidState target)
    (equivalent : MirrorRepresentativeEq source target) :
    MirrorRepresentativeEq target source := by
  rcases equivalent with same | mirrored
  · exact Or.inl (sameShape_symm same)
  · exact Or.inr
      ((sameShape_trans
        (sameShape_symm (mirror_sameShape mirrored))
        (observationalEq_sameShape
          (mirror_twice source
            (valid_horizontallyBounded sourceValid)))))

theorem mirrorRepresentativeEq_trans
    {source middle target : State}
    (sourceValid : ValidState source)
    (_middleValid : ValidState middle)
    (_targetValid : ValidState target)
    (first : MirrorRepresentativeEq source middle)
    (second : MirrorRepresentativeEq middle target) :
    MirrorRepresentativeEq source target := by
  rcases first with sameFirst | mirroredFirst
  · rcases second with sameSecond | mirroredSecond
    · exact Or.inl (sameShape_trans sameFirst sameSecond)
    · exact Or.inr
        (sameShape_trans (mirror_sameShape sameFirst) mirroredSecond)
  · rcases second with sameSecond | mirroredSecond
    · exact Or.inr (sameShape_trans mirroredFirst sameSecond)
    · exact Or.inl
        (sameShape_trans
          (sameShape_symm (observationalEq_sameShape
            (mirror_twice source
              (valid_horizontallyBounded sourceValid))))
          (sameShape_trans
            (mirror_sameShape mirroredFirst)
            mirroredSecond))

theorem mirrorRepresentativeEq_goal
    {source target : State}
    (sourceValid : ValidState source)
    (_targetValid : ValidState target)
    (equivalent : MirrorRepresentativeEq source target) :
    goal source = goal target := by
  rcases equivalent with same | mirrored
  · exact sameShape_goal same
  · have mirroredGoal :
        goal (mirrorState source) = goal source := by
      have goalIff :
          goal (mirrorState source) = true ↔ goal source = true := by
        rw [goal_eq_true_iff, goal_eq_true_iff]
        exact
          mirror_goal_iff source
            (valid_horizontallyBounded sourceValid)
      cases sourceGoal : goal source <;>
        cases reflectedGoal : goal (mirrorState source) <;>
        simp_all
    exact mirroredGoal.symm.trans (sameShape_goal mirrored)

/-- Transport a legal step between arbitrary representatives of a mirror class. -/
theorem mirrorRepresentativeEq_step_lift
    {source source' target : State}
    (sourceValid : ValidState source)
    (source'Valid : ValidState source')
    (equivalent : MirrorRepresentativeEq source source')
    (step : Step source target) :
    ∃ (action' : Action) (target' : State),
      tryMove source' action'.piece action'.direction = some target' ∧
      ValidState target' ∧
      MirrorRepresentativeEq target target' := by
  rcases step with ⟨action, executed⟩
  have targetValid := tryMove_preserves_validity executed
  rcases equivalent with same | mirrored
  · have lifted :=
      sameShapeStepLift
        (source := ⟨source, sourceValid⟩)
        (source' := ⟨source', source'Valid⟩)
        (target := ⟨target, targetValid⟩)
        (action := action)
        same executed
    rcases lifted with
      ⟨liftedAction, liftedTarget, liftedStep, targetEquivalent⟩
    exact ⟨liftedAction, liftedTarget.1,
      liftedStep, liftedTarget.2,
      Or.inl targetEquivalent⟩
  · have lifted :=
      sameShapeStepLift
        (source := ⟨mirrorState source, valid_mirror sourceValid⟩)
        (source' := ⟨source', source'Valid⟩)
        (target := ⟨mirrorState target, valid_mirror targetValid⟩)
        (action := ⟨action.piece, action.direction.mirror⟩)
        mirrored (mirror_tryMove sourceValid executed)
    rcases lifted with
      ⟨liftedAction, liftedTarget, liftedStep, targetEquivalent⟩
    exact ⟨liftedAction, liftedTarget.1,
      liftedStep, liftedTarget.2,
      Or.inr targetEquivalent⟩

def Graph.MirrorRepresents (graph : Graph)
    (state : State) (node : Fin graph.states.size) : Prop :=
  ValidState state ∧
  ValidState (graph.states.getD node classic) ∧
  MirrorRepresentativeEq state
    (graph.states.getD node classic)

def Graph.MirrorCertificateEdge (graph : Graph)
    (source target : Fin graph.states.size) : Prop :=
  ∃ edge next,
    edge ∈ graph.edges.toList ∧
    edge.source = source.1 ∧
    edge.target = target.1 ∧
    tryMove (graph.states.getD source classic) edge.piece edge.direction =
      some next ∧
    MirrorRepresentativeEq next
      (graph.states.getD target classic) ∧
    graph.distance.getD target 0 ≤
      graph.distance.getD source 0 + 1

def checkMirrorQuotientLowerBound
    (graph : Graph) (start : State) (bound : Nat) : Bool :=
  decide (0 < graph.states.size) &&
  checkMirrorValidStates graph &&
  checkMirrorStartRepresentation graph start &&
  decide (graph.distance.getD 0 0 = 0) &&
  checkMirrorEdgesComplete graph &&
  checkMirrorClosed graph &&
  checkMirrorGoalLowerBound graph bound

def Graph.mirrorQuotientLowerBoundCertificate
    (graph : Graph) (start : State) (bound : Nat)
    (nonempty : 0 < graph.states.size)
    (validStates : checkMirrorValidStates graph = true)
    (startChecked : checkMirrorStartRepresentation graph start = true)
    (rootDistance : graph.distance.getD 0 0 = 0)
    (edgesComplete : checkMirrorEdgesComplete graph = true)
    (_closed : checkMirrorClosed graph = true)
    (goals : checkMirrorGoalLowerBound graph bound) :
    QuotientLowerBoundCertificate start bound where
  Node := Fin graph.states.size
  Edge := graph.MirrorCertificateEdge
  represents := graph.MirrorRepresents
  startNode := ⟨0, nonempty⟩
  startRepresented := by
    rcases checkMirrorStartRepresentation_sound startChecked with
      ⟨startValid, sizePositive, startEquivalent⟩
    exact ⟨startValid,
      by
        simpa [Array.getD, nonempty] using
          checkMirrorValidStates_sound validStates 0 sizePositive,
      startEquivalent⟩
  simulateForward := by
    intro source target node represented step
    rcases represented with ⟨sourceValid, nodeValid, sourceEquivalent⟩
    have targetValid := step_preserves_validity sourceValid step
    rcases mirrorRepresentativeEq_step_lift
        sourceValid nodeValid sourceEquivalent step with
      ⟨liftedAction, next, liftedExecuted, nextValid, targetEquivalent⟩
    rcases checkMirrorEdgesComplete_sound edgesComplete node node.isLt
        liftedExecuted with
      ⟨targetIndex, targetEdge, targetLt, nextRepresented, targetEdgeMem,
        targetSource, targetTarget, targetPiece, targetDirection,
        targetEdgeChecked, distanceStep⟩
    let targetNode : Fin graph.states.size := ⟨targetIndex, targetLt⟩
    have targetNodeValid :
        ValidState (graph.states.getD targetNode.1 classic) := by
      simpa [targetNode, Array.getD, targetLt] using
        checkMirrorValidStates_sound validStates targetIndex targetLt
    have nextRepresented' :
        MirrorRepresentativeEq next
          (graph.states.getD targetNode.1 classic) := by
      simpa [targetNode, Array.getD, targetLt] using nextRepresented
    refine ⟨targetNode, ?_, ?_⟩
    · refine ⟨targetEdge, next, targetEdgeMem, targetSource, targetTarget,
        ?_, nextRepresented', distanceStep⟩
      · simpa [targetPiece, targetDirection] using liftedExecuted
    · exact ⟨targetValid, targetNodeValid,
        mirrorRepresentativeEq_trans
           targetValid nextValid
           targetNodeValid
           targetEquivalent nextRepresented'⟩
  simulateBackward := by
    intro source sourceNode targetNode represented edge
    rcases represented with ⟨sourceValid, sourceNodeValid, sourceEquivalent⟩
    rcases edge with
      ⟨storedEdge, next, _edgeMem, sourceEq, targetEq, executed,
        targetEquivalent, _distanceStep⟩
    have nextValid := tryMove_preserves_validity executed
    have targetNodeValid :
        ValidState (graph.states.getD targetNode.1 classic) := by
      simpa [Array.getD, targetNode.isLt] using
        checkMirrorValidStates_sound validStates targetNode.1 targetNode.isLt
    have targetEquivalent' :
        MirrorRepresentativeEq next
          (graph.states.getD targetNode.1 classic) := by
      simpa [Array.getD, targetNode.isLt] using targetEquivalent
    rcases mirrorRepresentativeEq_step_lift
        sourceNodeValid sourceValid
        (mirrorRepresentativeEq_symm sourceValid sourceNodeValid sourceEquivalent)
        ⟨⟨storedEdge.piece, storedEdge.direction⟩, executed⟩ with
      ⟨liftedAction, target, liftedExecuted, targetValid, nextToTarget⟩
    refine ⟨target, ⟨liftedAction, liftedExecuted⟩, ?_⟩
    exact ⟨targetValid, targetNodeValid,
      mirrorRepresentativeEq_trans
        targetValid nextValid
        targetNodeValid
        (mirrorRepresentativeEq_symm nextValid targetValid nextToTarget)
        targetEquivalent'⟩
  potential := fun node => graph.distance.getD node.1 0
  startPotential := rootDistance
  potentialStep := by
    intro source target edge
    rcases edge with
      ⟨_storedEdge, _next, _edgeMem, _sourceEq, _targetEq, _executed,
        _equivalent, distanceStep⟩
    exact distanceStep
  goalLowerBound := by
    intro target node represented isGoal
    have goalAtRepresentative :=
      mirrorRepresentativeEq_goal represented.1 represented.2.1 represented.2.2
    have representativeGoal :
        goal (graph.states.getD node.1 classic) = true := by
      exact goalAtRepresentative ▸ isGoal
    exact checkMirrorGoalLowerBound_sound goals node.1 node.isLt
      representativeGoal

theorem checkMirrorQuotientLowerBound_sound
    {graph : Graph} {start : State} {bound : Nat}
    (checked : checkMirrorQuotientLowerBound graph start bound = true) :
    Nonempty (QuotientLowerBoundCertificate start bound) := by
  unfold checkMirrorQuotientLowerBound at checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with
    ⟨⟨⟨⟨⟨⟨sizeChecked, validStates⟩,
      startChecked⟩, rootChecked⟩, edgesComplete⟩, closed⟩, goals⟩
  exact
    ⟨graph.mirrorQuotientLowerBoundCertificate start bound
      (of_decide_eq_true sizeChecked)
      validStates
      startChecked
      (of_decide_eq_true rootChecked)
      edgesComplete
      closed
      goals⟩

end Huarongdao
