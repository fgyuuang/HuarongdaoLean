import Huarongdao.Symmetry
import Huarongdao.StateSpace
import Huarongdao.Quotient
import Huarongdao.Enumeration

open Huarongdao

namespace Huarongdao

/-- Every valid classic state is horizontally bounded. -/
theorem valid_horizontallyBounded {s : State} (h : ValidState s) :
    HorizontallyBounded s := by
  intro p
  unfold ValidState valid at h
  rw [Bool.and_eq_true] at h
  rcases h with ⟨hBounds, _⟩
  unfold inBounds at hBounds
  rw [Bool.and_eq_true] at hBounds
  rcases hBounds with ⟨_, hAll⟩
  have hpRaw := (List.all_eq_true.mp hAll) p (Piece.mem_all p)
  rw [Bool.and_eq_true] at hpRaw
  exact of_decide_eq_true hpRaw.1

/-- The quotient by horizontal mirror symmetry on valid classic states. -/
def MirrorEquiv (s t : ValidClassicState) : Prop :=
  ObservationalEq s.1 t.1 ∨ ObservationalEq (mirrorState s.1) t.1

namespace MirrorEquiv

theorem refl (s : ValidClassicState) : MirrorEquiv s s :=
  Or.inl fun _ => rfl

theorem symm {s t : ValidClassicState} (h : MirrorEquiv s t) :
    MirrorEquiv t s := by
  rcases h with (hst | hst)
  · exact Or.inl fun p => (hst p).symm
  · have hb : HorizontallyBounded s.1 := valid_horizontallyBounded s.2
    have hmirror : ObservationalEq (mirrorState (mirrorState s.1)) s.1 :=
      mirror_twice s.1 hb
    exact Or.inr (by
      intro p
      have h1 : (mirrorState t.1).pos p = (mirrorState (mirrorState s.1)).pos p := by
        simp [hst p]
      exact h1.trans (hmirror p))

theorem trans {s t u : ValidClassicState} (hst : MirrorEquiv s t)
    (htu : MirrorEquiv t u) : MirrorEquiv s u := by
  rcases hst with (hst | hst)
  · rcases htu with (htu | htu)
    · exact Or.inl (by intro p; exact (hst p).trans (htu p))
    · exact Or.inr (by
        intro p
        calc
          (mirrorState s.1).pos p = mirrorPos p (s.1.pos p) := by simp
          _ = mirrorPos p (t.1.pos p) := by rw [hst p]
          _ = (mirrorState t.1).pos p := by simp
          _ = u.1.pos p := htu p)
  · rcases htu with (htu | htu)
    · exact Or.inr (by
        intro p
        calc
          (mirrorState s.1).pos p = mirrorPos p (s.1.pos p) := by simp
          _ = (mirrorState s.1).pos p := by simp
          _ = t.1.pos p := hst p
          _ = u.1.pos p := htu p)
    · have hs : ObservationalEq s.1 (mirrorState t.1) := by
        intro p
        have hb : HorizontallyBounded s.1 := valid_horizontallyBounded s.2
        have hmirror := mirror_twice s.1 hb
        calc
          s.1.pos p = (mirrorState (mirrorState s.1)).pos p := (hmirror p).symm
          _ = mirrorPos p ((mirrorState s.1).pos p) := by simp
          _ = mirrorPos p (t.1.pos p) := by rw [hst p]
          _ = (mirrorState t.1).pos p := by simp
      exact Or.inl (by
        intro p
        exact (hs p).trans (htu p))

end MirrorEquiv

/-- Horizontal mirror equivalence as a Setoid on valid classic states. -/
def mirrorSetoid : Setoid ValidClassicState where
  r := MirrorEquiv
  iseqv := {
    refl := MirrorEquiv.refl
    symm := MirrorEquiv.symm
    trans := MirrorEquiv.trans
  }
/-- A legal state remains legally bounded after horizontal mirroring. -/
theorem mirror_preserves_horizontallyBounded {s : State}
    (h : HorizontallyBounded s) : HorizontallyBounded (mirrorState s) := by
  intro p
  have hp := h p
  rcases hpos : s.pos p with ⟨x, y⟩
  simp only [mirrorState_pos, mirrorPos, hpos] at hp ⊢
  omega

def mirrorCell (pos : Pos) : Pos := ⟨3 - pos.x, pos.y⟩

private theorem range_two : List.range 2 = [0, 1] := by decide

theorem occupiedCells_mirror_perm {s : State}
    (h : HorizontallyBounded s) (p : Piece) :
    (occupiedCells (mirrorState s) p).Perm
      ((occupiedCells s p).map mirrorCell) := by
  have hp := h p
  rcases hpos : s.pos p with ⟨x, y⟩
  cases p <;>
    simp [occupiedCells, mirrorState_pos, mirrorPos, mirrorCell,
      Piece.shape, hpos] at hp ⊢
  all_goals simp [range_two, mirrorCell]
  case caoCao =>
    have hx : 2 - x + 1 = 3 - x := by omega
    rw [hx]
    exact
      (List.Perm.swap _ _ _).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ [])))
  case guanYu =>
    have hx : 2 - x + 1 = 3 - x := by omega
    rw [hx]
    exact List.Perm.swap _ _ []

theorem occupiedCell_x_lt {s : State} {p : Piece} {cell : Pos}
    (h : HorizontallyBounded s) (member : cell ∈ occupiedCells s p) :
    cell.x < 4 := by
  have hp := h p
  simp only [occupiedCells, List.mem_flatMap, List.mem_map] at member
  rcases member with ⟨dy, hdy, dx, hdx, hcell⟩
  subst cell
  have hdx' := List.mem_range.mp hdx
  simp only
  omega

theorem mirrorCell_injective_of_lt {a b : Pos}
    (ha : a.x < 4) (hb : b.x < 4)
    (h : mirrorCell a = mirrorCell b) : a = b := by
  cases a with
  | mk ax ay =>
    cases b with
    | mk bx byy =>
      simp only [mirrorCell] at h
      have hx := congrArg Pos.x h
      have hy := congrArg Pos.y h
      simp only at ha hb hx hy
      congr <;> omega

theorem inBounds_mirror {s : State} (h : inBounds s = true) :
    inBounds (mirrorState s) = true := by
  unfold inBounds at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  rcases h with ⟨_, hall⟩
  constructor
  · simp [mirrorState, State.ofFn, Piece.all]
  · apply List.all_eq_true.mpr
    intro p hp
    have horig := (List.all_eq_true.mp hall) p hp
    rw [Bool.and_eq_true] at horig ⊢
    rcases horig with ⟨hx, hy⟩
    constructor
    · have hx' := of_decide_eq_true hx
      rcases hpos : s.pos p with ⟨x, y⟩
      cases p <;>
        simp [mirrorState_pos, mirrorPos, Piece.shape, hpos] at hx' ⊢ <;>
        omega
    · simpa [mirrorState_pos, mirrorPos] using hy

theorem noOverlap_mirror {s : State} (hbound : HorizontallyBounded s)
    (h : noOverlap s = true) : noOverlap (mirrorState s) = true := by
  unfold noOverlap at h ⊢
  apply List.all_eq_true.mpr
  intro p hp
  apply List.all_eq_true.mpr
  intro q hq
  by_cases hpq : p = q
  · subst q
    cases p <;> rfl
  · have horig := (List.all_eq_true.mp ((List.all_eq_true.mp h) p hp)) q hq
    have hpqBool : (p == q) = false := by
      cases p <;> cases q <;> first | contradiction | rfl
    rw [hpqBool] at horig ⊢
    simp only [Bool.false_or] at horig ⊢
    apply List.all_eq_true.mpr
    intro a ha
    apply List.all_eq_true.mpr
    intro b hb
    have hpa := occupiedCells_mirror_perm hbound p
    have hqb := occupiedCells_mirror_perm hbound q
    have haMap : a ∈ (occupiedCells s p).map mirrorCell :=
      (hpa.mem_iff).mp ha
    have hbMap : b ∈ (occupiedCells s q).map mirrorCell :=
      (hqb.mem_iff).mp hb
    rcases List.mem_map.mp haMap with ⟨a0, ha0, rfl⟩
    rcases List.mem_map.mp hbMap with ⟨b0, hb0, rfl⟩
    have hneqBool :=
      (List.all_eq_true.mp ((List.all_eq_true.mp horig) a0 ha0)) b0 hb0
    have hneq : a0 ≠ b0 := bne_iff_ne.mp hneqBool
    have mirroredNeq : mirrorCell a0 ≠ mirrorCell b0 := by
      intro heq
      exact hneq (mirrorCell_injective_of_lt
        (occupiedCell_x_lt hbound ha0)
        (occupiedCell_x_lt hbound hb0) heq)
    exact bne_iff_ne.mpr mirroredNeq

theorem valid_mirror {s : State} (h : ValidState s) : ValidState (mirrorState s) := by
  have hbound := valid_horizontallyBounded h
  unfold ValidState valid at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨inBounds_mirror h.1, noOverlap_mirror hbound h.2⟩

theorem mirror_translated_of_some {p : Piece} {pos next : Pos}
    {d : Direction}
    (sourceBound : pos.x + p.shape.width ≤ 4)
    (targetBound : next.x + p.shape.width ≤ 4)
    (translated_eq : translated pos d = some next) :
    translated (mirrorPos p pos) d.mirror =
      some (mirrorPos p next) := by
  cases d with
  | up =>
      rcases pos with ⟨x, y⟩
      by_cases hy : y = 0
      · simp [translated, hy] at translated_eq
      · simp [translated, hy] at translated_eq
        subst next
        simp [translated, hy, mirrorPos, Direction.mirror]
  | down =>
      rcases pos with ⟨x, y⟩
      simp [translated] at translated_eq
      subst next
      simp [translated, mirrorPos, Direction.mirror]
  | left =>
      rcases pos with ⟨x, y⟩
      by_cases hx : x = 0
      · simp [translated, hx] at translated_eq
      · simp [translated, hx] at translated_eq
        subst next
        simp only at sourceBound targetBound
        simp [translated, mirrorPos, Direction.mirror]
        omega
  | right =>
      rcases pos with ⟨x, y⟩
      simp [translated] at translated_eq
      subst next
      simp only at sourceBound targetBound
      have mirrorPositive : 4 - (x + p.shape.width) ≠ 0 := by omega
      simp [translated, mirrorPositive, mirrorPos, Direction.mirror]
      omega

theorem mirror_moveUnchecked {s t : State} {p : Piece} {d : Direction}
    (sourceBound : HorizontallyBounded s)
    (targetBound : HorizontallyBounded t)
    (h : moveUnchecked s p d = some t) :
    moveUnchecked (mirrorState s) p d.mirror = some (mirrorState t) := by
  unfold moveUnchecked at h
  cases ht : translated (s.pos p) d with
  | none => simp [ht] at h
  | some next =>
      simp [ht] at h
      subst t
      have nextBound : next.x + p.shape.width ≤ 4 := by
        have hp := targetBound p
        simpa [State.ofFn_pos] using hp
      have mirroredTranslation :=
        mirror_translated_of_some (sourceBound p) nextBound ht
      unfold moveUnchecked
      simp [mirrorState_pos, mirroredTranslation]
      congr 1
      ext q
      by_cases hqp : q = p <;> simp [State.ofFn_pos, hqp]

/-- Legal one-step moves commute with horizontal mirroring. -/
theorem mirror_tryMove {s t : State} {p : Piece} {d : Direction}
    (hs : ValidState s) (h : tryMove s p d = some t) :
    tryMove (mirrorState s) p d.mirror = some (mirrorState t) := by
  have ht : ValidState t := tryMove_preserves_validity h
  have sourceBound := valid_horizontallyBounded hs
  have targetBound := valid_horizontallyBounded ht
  unfold tryMove at h ⊢
  cases hmu : moveUnchecked s p d with
  | none => simp [hmu] at h
  | some candidate =>
      by_cases hvalid : valid candidate = true
      · simp [hmu, hvalid] at h
        subst t
        have mirroredMove := mirror_moveUnchecked sourceBound targetBound hmu
        have mirroredValid : valid (mirrorState candidate) = true := by
          exact valid_mirror hvalid
        simp [mirroredMove, mirroredValid]
      · simp [hmu, hvalid] at h

namespace MirrorObservation

theorem goal_bool_iff (s : State) : goal s = true ↔ GoalState s :=
  goal_eq_true_iff s

theorem goal_iff {s t : ValidClassicState} (h : MirrorEquiv s t) :
    (validClassicTask.goal s ↔ validClassicTask.goal t) := by
  rcases h with (same | mirrored)
  · change goal s.1 = true ↔ goal t.1 = true
    unfold goal
    rw [same .caoCao]
  · have hb : HorizontallyBounded s.1 := valid_horizontallyBounded s.2
    have hgoalmirror : GoalState (mirrorState s.1) ↔ GoalState s.1 :=
      mirror_goal_iff s.1 hb
    have hmpos : (mirrorState s.1).pos .caoCao = t.1.pos .caoCao := mirrored .caoCao
    have hmpos_goal : GoalState t.1 ↔ GoalState (mirrorState s.1) := by
      constructor
      · intro hgoal
        change (mirrorState s.1).pos .caoCao = ⟨1, 3⟩
        exact hmpos ▸ hgoal
      · intro hg
        change t.1.pos .caoCao = ⟨1, 3⟩
        exact hmpos.symm ▸ hg
    constructor
    · intro hgoal
      have hgs : GoalState s.1 := by
        change goal s.1 = true at hgoal
        exact (goal_eq_true_iff s.1).mp hgoal
      have hgm : GoalState (mirrorState s.1) := hgoalmirror.mpr hgs
      change goal t.1 = true
      change goal t.1 = true
      exact (goal_eq_true_iff t.1).mpr (hmpos_goal.mpr hgm)
    · intro hgoal
      have hgt : GoalState t.1 := by
        change goal t.1 = true at hgoal
        exact (goal_eq_true_iff t.1).mp hgoal
      have hgm : GoalState (mirrorState s.1) := hmpos_goal.mp hgt
      have hgs : GoalState s.1 := hgoalmirror.mp hgm
      change goal s.1 = true
      change goal s.1 = true
      exact (goal_eq_true_iff s.1).mpr hgs

end MirrorObservation

/-- The goal predicate descends to horizontal-mirror classes. -/
def mirrorObservation : StateSpace.Observation validClassicTask where
  setoid := mirrorSetoid
  goal_iff := MirrorObservation.goal_iff

namespace MirrorBisimulation

/-- Step lifting obligation for the horizontal mirror quotient. -/
def MirrorStepLift : Prop :=
  ∀ {source source' : ValidClassicState} {action : Action}
      {target : ValidClassicState},
    MirrorEquiv source source' →
    validClassicTask.step source action target →
    ∃ action' target',
      validClassicTask.step source' action' target' ∧
      MirrorEquiv target target'

/-- Package a completed mirror move-equivariance proof as an exact quotient. -/
def mirrorBisimulation (step_lift : MirrorStepLift) :
    StateSpace.BisimulationQuotient validClassicTask where
  toObservation := mirrorObservation
  step_lift := by
    intro source source' action target equiv step
    exact step_lift equiv step

end MirrorBisimulation

/-!
The executable graph first quotients equal-shaped piece labels and only then
identifies horizontal mirror orbits.  The definitions below formalize exactly
that second quotient on `ShapeState`.
-/

/-- Horizontal mirroring respects the existing equal-shape quotient. -/
theorem mirror_sameShape {s t : State} (h : SameShape s t) :
    SameShape (mirrorState s) (mirrorState t) := by
  rcases h with ⟨hcao, hguan, hvertical, hsoldier⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mirrorState_pos]
    rw [hcao]
  · simp only [mirrorState_pos]
    rw [hguan]
  · simpa [verticalPositions, mirrorState_pos, mirrorPos, Piece.shape,
      mirrorCell] using hvertical.map mirrorCell
  · simpa [soldierPositions, mirrorState_pos, mirrorPos, Piece.shape,
      mirrorCell] using hsoldier.map mirrorCell

/-- Mirror a valid labelled state while retaining its validity proof. -/
def mirrorValidState (state : ValidClassicState) : ValidClassicState :=
  ⟨mirrorState state.1, valid_mirror state.2⟩

/-- The induced horizontal-mirror automorphism on equal-shape classes. -/
def mirrorShapeState (node : ShapeState) : ShapeState :=
  Quotient.liftOn node
    (fun state => ShapeState.ofState (mirrorValidState state))
    (by
      intro source target sameShape
      exact Quotient.sound (mirror_sameShape sameShape))

@[simp] theorem mirrorShapeState_ofState (state : ValidClassicState) :
    mirrorShapeState (ShapeState.ofState state) =
      ShapeState.ofState (mirrorValidState state) :=
  rfl

theorem observationalEq_sameShape {s t : State}
    (h : ObservationalEq s t) : SameShape s t := by
  refine ⟨h .caoCao, h .guanYu, ?_, ?_⟩
  · apply List.Perm.of_eq
    simp only [verticalPositions, List.map]
    rw [h .zhangFei, h .zhaoYun, h .maChao, h .huangZhong]
  · apply List.Perm.of_eq
    simp only [soldierPositions, List.map]
    rw [h .soldier1, h .soldier2, h .soldier3, h .soldier4]

/-- The induced mirror on shape classes is an involution. -/
@[simp] theorem mirrorShapeState_involutive (node : ShapeState) :
    mirrorShapeState (mirrorShapeState node) = node := by
  refine Quotient.inductionOn node ?_
  intro state
  apply Quotient.sound
  exact observationalEq_sameShape
    (mirror_twice state.1 (valid_horizontallyBounded state.2))

/-- Equality up to one application of horizontal mirror on shape classes. -/
def ShapeMirrorEquiv (source target : ShapeState) : Prop :=
  source = target ∨ mirrorShapeState source = target

namespace ShapeMirrorEquiv

theorem refl (node : ShapeState) : ShapeMirrorEquiv node node :=
  Or.inl rfl

theorem symm {source target : ShapeState}
    (h : ShapeMirrorEquiv source target) :
    ShapeMirrorEquiv target source := by
  rcases h with equal | mirrored
  · exact Or.inl equal.symm
  · exact Or.inr (by
      calc
        mirrorShapeState target =
            mirrorShapeState (mirrorShapeState source) := by rw [mirrored]
        _ = source := mirrorShapeState_involutive source)

theorem trans {source middle target : ShapeState}
    (hsm : ShapeMirrorEquiv source middle)
    (hmt : ShapeMirrorEquiv middle target) :
    ShapeMirrorEquiv source target := by
  rcases hsm with equalSM | mirrorSM
  · rcases hmt with equalMT | mirrorMT
    · exact Or.inl (equalSM.trans equalMT)
    · exact Or.inr (by simpa [equalSM] using mirrorMT)
  · rcases hmt with equalMT | mirrorMT
    · exact Or.inr (mirrorSM.trans equalMT)
    · exact Or.inl (by
        calc
          source = mirrorShapeState (mirrorShapeState source) :=
            (mirrorShapeState_involutive source).symm
          _ = mirrorShapeState middle := by rw [mirrorSM]
          _ = target := mirrorMT)

end ShapeMirrorEquiv

/-- The setoid used by the maintained mirror quotient graph. -/
def shapeMirrorSetoid : Setoid ShapeState where
  r := ShapeMirrorEquiv
  iseqv := {
    refl := ShapeMirrorEquiv.refl
    symm := ShapeMirrorEquiv.symm
    trans := ShapeMirrorEquiv.trans
  }

/-- Nodes of the formal graph after equal-shape and horizontal-mirror quotienting. -/
abbrev MirrorShapeState := Quotient shapeMirrorSetoid

/-- Horizontal mirroring preserves the goal predicate on shape classes. -/
theorem mirrorShape_goal_iff (node : ShapeState) :
    shapeObservation.Goal (mirrorShapeState node) ↔
      shapeObservation.Goal node := by
  refine Quotient.inductionOn node ?_
  intro state
  change goal (mirrorState state.1) = true ↔ goal state.1 = true
  rw [goal_eq_true_iff, goal_eq_true_iff]
  exact mirror_goal_iff state.1 (valid_horizontallyBounded state.2)

/-- Every edge of the equal-shape graph has a horizontally mirrored edge. -/
theorem shapeStep_mirror {source target : ShapeState}
    (h : ShapeStep source target) :
    ShapeStep (mirrorShapeState source) (mirrorShapeState target) := by
  rcases h with ⟨sourceState, targetState, sourceEq, targetEq,
    ⟨action, executed⟩⟩
  refine ⟨mirrorValidState sourceState, mirrorValidState targetState,
    ?_, ?_, ?_⟩
  · simpa using congrArg mirrorShapeState sourceEq
  · simpa using congrArg mirrorShapeState targetEq
  · exact ⟨⟨action.piece, action.direction.mirror⟩,
      mirror_tryMove sourceState.2 executed⟩

/-- The exact equal-shape quotient, represented by the common task object. -/
def shapeGraphTask : StateSpace.Task ShapeState Unit :=
  shapeObservation.quotientTask

/-- The horizontal-mirror observation of the maintained equal-shape graph. -/
def mirrorShapeObservation : StateSpace.Observation shapeGraphTask where
  setoid := shapeMirrorSetoid
  goal_iff := by
    intro source target equivalent
    rcases equivalent with equal | mirrored
    · subst target
      exact Iff.rfl
    · rw [← mirrored]
      exact (mirrorShape_goal_iff source).symm

/--
The mirror quotient is an exact bisimulation quotient of the equal-shape
graph.  Consequently, quotient walks lift from every representative.
-/
def mirrorShapeBisimulation :
    StateSpace.BisimulationQuotient shapeGraphTask where
  toObservation := mirrorShapeObservation
  step_lift := by
    intro source source' action target equivalent step
    rcases equivalent with equal | mirrored
    · subst source'
      exact ⟨action, target, step, Or.inl rfl⟩
    · refine ⟨(), mirrorShapeState target, ?_, Or.inr rfl⟩
      rw [← mirrored]
      apply (shapeStep_iff_observationStep _ _).mp
      exact shapeStep_mirror
        ((shapeStep_iff_observationStep _ _).mpr step)

namespace MirrorShapeState

/-- Insert an equal-shape node into the maintained mirror quotient. -/
def ofShapeState (node : ShapeState) : MirrorShapeState :=
  Quotient.mk shapeMirrorSetoid node

/-- Insert a valid concrete state into the two-stage quotient. -/
def ofState (state : ValidClassicState) : MirrorShapeState :=
  ofShapeState (ShapeState.ofState state)

/-- A shape node and its horizontal mirror are literally the same quotient node. -/
theorem ofShapeState_mirror (node : ShapeState) :
    ofShapeState (mirrorShapeState node) = ofShapeState node :=
  Quotient.sound (Or.inr (mirrorShapeState_involutive node))

end MirrorShapeState

/-- Directed edges of the maintained mirror quotient graph. -/
def MirrorShapeStep (source target : MirrorShapeState) : Prop :=
  mirrorShapeObservation.Step source target

/-- Goal nodes of the maintained mirror quotient graph. -/
def MirrorShapeGoal (node : MirrorShapeState) : Prop :=
  mirrorShapeObservation.Goal node

/-- The exact mirror quotient, represented by the common task object. -/
def mirrorShapeTask : StateSpace.Task MirrorShapeState Unit :=
  mirrorShapeObservation.quotientTask

/-- Every equal-shape edge projects to one formal mirror-quotient edge. -/
theorem mirrorShapeStep_of_shapeStep {source target : ShapeState}
    (h : ShapeStep source target) :
    MirrorShapeStep
      (MirrorShapeState.ofShapeState source)
      (MirrorShapeState.ofShapeState target) :=
  mirrorShapeObservation.step_of_step (action := ())
    ((shapeStep_iff_observationStep _ _).mp h)

/-- Every exact legal move between valid boards projects to the maintained graph. -/
theorem mirrorShapeStep_of_step {source target : State}
    (sourceValid : ValidState source) (targetValid : ValidState target)
    (h : Step source target) :
    MirrorShapeStep
      (MirrorShapeState.ofState ⟨source, sourceValid⟩)
      (MirrorShapeState.ofState ⟨target, targetValid⟩) :=
  mirrorShapeStep_of_shapeStep
    (shapeStep_of_step sourceValid targetValid h)

/-- The quotient goal at a concrete representative is exactly the puzzle goal. -/
theorem mirrorShapeGoal_ofState_iff (state : ValidClassicState) :
    MirrorShapeGoal (MirrorShapeState.ofState state) ↔
      goal state.1 = true :=
  Iff.rfl

/--
Every walk in the maintained mirror quotient lifts to an equal-length walk in
the pre-mirror equal-shape graph, from any chosen source representative.
-/
theorem mirrorShapeQuotient_liftWalkWithLength
    {sourceClass targetClass : MirrorShapeState}
    (walk : mirrorShapeObservation.QuotientWalk sourceClass targetClass)
    (source : ShapeState)
    (source_eq : MirrorShapeState.ofShapeState source = sourceClass) :
    ∃ target, ∃ concreteWalk : shapeGraphTask.Walk source target,
      concreteWalk.length = walk.length ∧
      MirrorShapeState.ofShapeState target = targetClass :=
  mirrorShapeBisimulation.liftWalkWithLength walk source source_eq

/-- Task-level lifting from the mirror quotient to the equal-shape quotient. -/
theorem mirrorShapeTask_liftWalkWithLength
    {sourceClass targetClass : MirrorShapeState}
    (walk : mirrorShapeTask.Walk sourceClass targetClass)
    (source : ShapeState)
    (source_eq : MirrorShapeState.ofShapeState source = sourceClass) :
    ∃ target, ∃ shapeWalk : shapeGraphTask.Walk source target,
      shapeWalk.length = walk.length ∧
      MirrorShapeState.ofShapeState target = targetClass :=
  mirrorShapeBisimulation.liftTaskWalkWithLength walk source source_eq

/-- Task-level lifting from the equal-shape quotient to concrete valid states. -/
theorem shapeTask_liftWalkWithLength
    {sourceClass targetClass : ShapeState}
    (walk : shapeGraphTask.Walk sourceClass targetClass)
    (source : ValidClassicState)
    (source_eq : ShapeState.ofState source = sourceClass) :
    ∃ target, ∃ concreteWalk : validClassicTask.Walk source target,
      concreteWalk.length = walk.length ∧
      ShapeState.ofState target = targetClass :=
  shapeBisimulation.liftTaskWalkWithLength walk source source_eq

/--
The complete two-stage quotient chain lifts every mirror-quotient walk to an
equal-length concrete walk between valid labelled states.
-/
theorem mirrorShapeTask_liftToConcreteWithLength
    {sourceClass targetClass : MirrorShapeState}
    (walk : mirrorShapeTask.Walk sourceClass targetClass)
    (source : ValidClassicState)
    (source_eq : MirrorShapeState.ofState source = sourceClass) :
    ∃ target, ∃ concreteWalk : validClassicTask.Walk source target,
      concreteWalk.length = walk.length ∧
      MirrorShapeState.ofState target = targetClass := by
  rcases mirrorShapeTask_liftWalkWithLength walk
      (ShapeState.ofState source) source_eq with
    ⟨shapeTarget, shapeWalk, shapeLength, mirrorTarget⟩
  rcases shapeTask_liftWalkWithLength shapeWalk source rfl with
    ⟨target, concreteWalk, concreteLength, shapeTargetEq⟩
  refine ⟨target, concreteWalk, concreteLength.trans shapeLength, ?_⟩
  exact congrArg MirrorShapeState.ofShapeState shapeTargetEq |>.trans
    mirrorTarget

end Huarongdao
