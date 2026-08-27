import Huarongdao.Paths
import Huarongdao.Enumeration
import Std.Tactic

namespace Huarongdao

def verticalPositions (s : State) : List Pos :=
  [.zhangFei, .zhaoYun, .maChao, .huangZhong].map s.pos

def soldierPositions (s : State) : List Pos :=
  [.soldier1, .soldier2, .soldier3, .soldier4].map s.pos

/-- Geometric equality after forgetting labels of equal-shaped pieces. -/
def SameShape (s t : State) : Prop :=
  s.pos .caoCao = t.pos .caoCao ∧
  s.pos .guanYu = t.pos .guanYu ∧
  (verticalPositions s).Perm (verticalPositions t) ∧
  (soldierPositions s).Perm (soldierPositions t)

instance (s t : State) : Decidable (SameShape s t) := by
  unfold SameShape
  infer_instance

theorem sameShape_refl (s : State) : SameShape s s :=
  ⟨rfl, rfl, .refl _, .refl _⟩

theorem sameShape_symm {s t : State} (h : SameShape s t) : SameShape t s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem sameShape_trans {s t u : State} (hst : SameShape s t)
    (htu : SameShape t u) : SameShape s u :=
  ⟨hst.1.trans htu.1, hst.2.1.trans htu.2.1,
   hst.2.2.1.trans htu.2.2.1, hst.2.2.2.trans htu.2.2.2⟩

theorem sameShape_goal {s t : State} (h : SameShape s t) : goal s = goal t := by
  simp only [goal]
  rw [h.1]

/-- A quotient edge: an exact move followed by harmless relabeling. -/
def QStep (s t : State) : Prop :=
  ∃ p d next, tryMove s p d = some next ∧ SameShape next t

theorem step_to_qstep {s t : State} (h : Step s t) : QStep s t := by
  rcases h with ⟨action, ha⟩
  exact ⟨action.piece, action.direction, t, ha, sameShape_refl t⟩

/-- A proof-carrying path through the quotient graph.  Each step stores both
    the exact executable successor and the proof that the displayed target is
    merely an equal-shape representative. -/
inductive QPath : State → State → Type where
  | nil (s : State) : QPath s s
  | cons {s actual next target : State} (action : Action)
      (executed : tryMove s action.piece action.direction = some actual)
      (represented : SameShape actual next)
      (tail : QPath next target) : QPath s target

namespace QPath

def length : QPath s t → Nat
  | .nil _ => 0
  | .cons _ _ _ tail => tail.length + 1

/-- Every exact Path is also a quotient path, using reflexive representatives. -/
def ofPath : Path s t → QPath s t
  | .nil _ => .nil _
  | .cons action executed tail =>
      .cons action executed (sameShape_refl _) (ofPath tail)

end QPath

/-- A completed solution in the equal-shape quotient transition system. -/
structure QSolution (start : State) where
  target : State
  path : QPath start target
  solved : goal target = true

structure PieceRelabeling where
  forward : Piece → Piece
  inverse : Piece → Piece
  leftInv : ∀ p, inverse (forward p) = p
  rightInv : ∀ p, forward (inverse p) = p
  fixedCao : forward .caoCao = .caoCao
  fixedGuan : forward .guanYu = .guanYu
  shape_preserving : ∀ p, (forward p).shape = p.shape

def PieceRelabeling.symm (σ : PieceRelabeling) : PieceRelabeling where
  forward := σ.inverse
  inverse := σ.forward
  leftInv := σ.rightInv
  rightInv := σ.leftInv
  fixedCao := by
    calc
      σ.inverse .caoCao = σ.inverse (σ.forward .caoCao) := congrArg σ.inverse σ.fixedCao.symm
      _ = .caoCao := σ.leftInv _
  fixedGuan := by
    calc
      σ.inverse .guanYu = σ.inverse (σ.forward .guanYu) := congrArg σ.inverse σ.fixedGuan.symm
      _ = .guanYu := σ.leftInv _
  shape_preserving := by
    intro p
    have h := σ.shape_preserving (σ.inverse p)
    rw [σ.rightInv] at h
    exact h.symm

def PieceRelabeling.identity : PieceRelabeling where
  forward := id
  inverse := id
  leftInv := by intro p; rfl
  rightInv := by intro p; rfl
  fixedCao := rfl
  fixedGuan := rfl
  shape_preserving := by intro p; rfl

/-- Composition corresponding to applying `inner` first and `outer` second. -/
def PieceRelabeling.comp (outer inner : PieceRelabeling) : PieceRelabeling where
  forward := fun p => outer.forward (inner.forward p)
  inverse := fun p => inner.inverse (outer.inverse p)
  leftInv := by intro p; rw [outer.leftInv, inner.leftInv]
  rightInv := by intro p; rw [inner.rightInv, outer.rightInv]
  fixedCao := by rw [inner.fixedCao, outer.fixedCao]
  fixedGuan := by rw [inner.fixedGuan, outer.fixedGuan]
  shape_preserving := by
    intro p
    rw [outer.shape_preserving, inner.shape_preserving]

def relabelState (σ : PieceRelabeling) (s : State) : State :=
  State.ofFn fun p => s.pos (σ.inverse p)

@[simp] theorem relabelState_pos (σ : PieceRelabeling) (s : State) (p : Piece) :
    (relabelState σ s).pos p = s.pos (σ.inverse p) := by
  simp [relabelState]

theorem relabel_forward_pos (σ : PieceRelabeling) (s : State) (p : Piece) :
    (relabelState σ s).pos (σ.forward p) = s.pos p := by
  rw [relabelState_pos, σ.leftInv]

def ObservationalEq (s t : State) : Prop := ∀ p, s.pos p = t.pos p

theorem relabel_inverse (σ : PieceRelabeling) (s : State) :
    ObservationalEq (relabelState σ.symm (relabelState σ s)) s := by
  intro p
  rw [relabelState_pos, relabelState_pos]
  change s.pos (σ.inverse (σ.forward p)) = s.pos p
  rw [σ.leftInv]

theorem goal_relabel (σ : PieceRelabeling) (s : State) :
    goal (relabelState σ s) = goal s := by
  simp only [goal, relabelState_pos]
  have hc : σ.inverse .caoCao = .caoCao := σ.symm.fixedCao
  rw [hc]

def swapSoldiers12Piece : Piece → Piece
  | .soldier1 => .soldier2
  | .soldier2 => .soldier1
  | p => p

def swapSoldiers12 : PieceRelabeling where
  forward := swapSoldiers12Piece
  inverse := swapSoldiers12Piece
  leftInv := by intro p; cases p <;> rfl
  rightInv := by intro p; cases p <;> rfl
  fixedCao := rfl
  fixedGuan := rfl
  shape_preserving := by intro p; cases p <;> rfl

def PieceRelabeling.ofInvolution (f : Piece → Piece)
    (involutive : ∀ p, f (f p) = p)
    (fixedCao : f .caoCao = .caoCao)
    (fixedGuan : f .guanYu = .guanYu)
    (shape_preserving : ∀ p, (f p).shape = p.shape) : PieceRelabeling where
  forward := f
  inverse := f
  leftInv := involutive
  rightInv := involutive
  fixedCao := fixedCao
  fixedGuan := fixedGuan
  shape_preserving := shape_preserving

def swapVertical12Piece : Piece → Piece
  | .zhangFei => .zhaoYun
  | .zhaoYun => .zhangFei
  | p => p

def swapVertical23Piece : Piece → Piece
  | .zhaoYun => .maChao
  | .maChao => .zhaoYun
  | p => p

def swapVertical34Piece : Piece → Piece
  | .maChao => .huangZhong
  | .huangZhong => .maChao
  | p => p

def swapSoldiers23Piece : Piece → Piece
  | .soldier2 => .soldier3
  | .soldier3 => .soldier2
  | p => p

def swapSoldiers34Piece : Piece → Piece
  | .soldier3 => .soldier4
  | .soldier4 => .soldier3
  | p => p

def swapVertical12 : PieceRelabeling := PieceRelabeling.ofInvolution swapVertical12Piece
  (by intro p; cases p <;> rfl) rfl rfl (by intro p; cases p <;> rfl)

def swapVertical23 : PieceRelabeling := PieceRelabeling.ofInvolution swapVertical23Piece
  (by intro p; cases p <;> rfl) rfl rfl (by intro p; cases p <;> rfl)

def swapVertical34 : PieceRelabeling := PieceRelabeling.ofInvolution swapVertical34Piece
  (by intro p; cases p <;> rfl) rfl rfl (by intro p; cases p <;> rfl)

def swapSoldiers23 : PieceRelabeling := PieceRelabeling.ofInvolution swapSoldiers23Piece
  (by intro p; cases p <;> rfl) rfl rfl (by intro p; cases p <;> rfl)

def swapSoldiers34 : PieceRelabeling := PieceRelabeling.ofInvolution swapSoldiers34Piece
  (by intro p; cases p <;> rfl) rfl rfl (by intro p; cases p <;> rfl)

/-- The 24 permutations generated by three adjacent transpositions. -/
def PieceRelabeling.permutations4
    (swap12 swap23 swap34 : PieceRelabeling) : List PieceRelabeling :=
  let base := [identity, swap12, swap23, swap12.comp swap23,
    swap23.comp swap12, swap12.comp (swap23.comp swap12)]
  let moveFourth := [identity, swap34, swap23.comp swap34,
    swap12.comp (swap23.comp swap34)]
  base.flatMap fun σ => moveFourth.map fun τ => τ.comp σ

def verticalRelabelings : List PieceRelabeling :=
  PieceRelabeling.permutations4 swapVertical12 swapVertical23 swapVertical34

def soldierRelabelings : List PieceRelabeling :=
  PieceRelabeling.permutations4 swapSoldiers12 swapSoldiers23 swapSoldiers34

/-- All 4! × 4! label permutations that preserve the two interchangeable groups. -/
def shapeRelabelings : List PieceRelabeling :=
  verticalRelabelings.flatMap fun vertical =>
    soldierRelabelings.map fun soldier => vertical.comp soldier

def matchesPieces (pieces : List Piece) (source representative : State)
    (σ : PieceRelabeling) : Bool :=
  pieces.all fun p => source.pos p == representative.pos (σ.inverse p)

def findShapeRelabeling (source representative : State) : Option PieceRelabeling := do
  let vertical ← verticalRelabelings.find? <|
    matchesPieces [.zhangFei, .zhaoYun, .maChao, .huangZhong] source representative
  let soldier ← soldierRelabelings.find? <|
    matchesPieces [.soldier1, .soldier2, .soldier3, .soldier4] source representative
  let combined := vertical.comp soldier
  if relabelState combined representative == source then some combined else none

theorem findShapeRelabeling_sound {source representative : State} {σ : PieceRelabeling}
    (h : findShapeRelabeling source representative = some σ) :
    relabelState σ representative = source := by
  unfold findShapeRelabeling at h
  cases hv : verticalRelabelings.find? <|
      matchesPieces [.zhangFei, .zhaoYun, .maChao, .huangZhong] source representative with
  | none => simp [hv] at h
  | some vertical =>
      cases hs : soldierRelabelings.find? <|
          matchesPieces [.soldier1, .soldier2, .soldier3, .soldier4] source representative with
      | none => simp [hv, hs] at h
      | some soldier =>
          simp only [hv, hs] at h
          by_cases hexact : relabelState (vertical.comp soldier) representative == source
          · simp at h
            rw [← h.2]
            exact h.1
          · simp at h
            exact False.elim (hexact (beq_iff_eq.mpr h.1))

theorem swapSoldiers12_sameShape (s : State) :
    SameShape (relabelState swapSoldiers12 s) s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact .refl _
  · exact List.Perm.swap _ _ _

theorem PieceRelabeling.inverse_injective (σ : PieceRelabeling) :
    Function.Injective σ.inverse := by
  intro p q h
  have mapped := congrArg σ.forward h
  simpa only [σ.rightInv] using mapped

theorem occupiedCells_relabel (σ : PieceRelabeling) (s : State) (p : Piece) :
    occupiedCells (relabelState σ s) p = occupiedCells s (σ.inverse p) := by
  unfold occupiedCells
  rw [relabelState_pos]
  have shape := σ.symm.shape_preserving p
  change (σ.inverse p).shape = p.shape at shape
  rw [shape]

theorem inBounds_relabel (σ : PieceRelabeling) {s : State}
    (h : inBounds s = true) : inBounds (relabelState σ s) = true := by
  unfold inBounds at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨rfl, ?_⟩
  rw [List.all_eq_true] at h ⊢
  intro p _
  have bound := h.2 (σ.inverse p) (σ.inverse p).mem_all
  have shape := σ.symm.shape_preserving p
  change (σ.inverse p).shape = p.shape at shape
  simpa only [relabelState_pos, shape] using bound

theorem noOverlap_relabel (σ : PieceRelabeling) {s : State}
    (h : noOverlap s = true) : noOverlap (relabelState σ s) = true := by
  unfold noOverlap at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro p _
  rw [List.all_eq_true]
  intro q _
  rw [Bool.or_eq_true]
  by_cases hpq : p = q
  · exact Or.inl (beq_iff_eq.mpr hpq)
  · have hinv : σ.inverse p ≠ σ.inverse q := fun heq => hpq (σ.inverse_injective heq)
    have separated := h (σ.inverse p) (σ.inverse p).mem_all
    rw [List.all_eq_true] at separated
    have separated := separated (σ.inverse q) (σ.inverse q).mem_all
    rw [Bool.or_eq_true] at separated
    have disjoint := separated.resolve_left (fun heq => hinv (beq_iff_eq.mp heq))
    exact Or.inr (by simpa only [occupiedCells_relabel] using disjoint)

theorem valid_relabel (σ : PieceRelabeling) {s : State}
    (h : valid s = true) : valid (relabelState σ s) = true := by
  unfold valid at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨inBounds_relabel σ h.1, noOverlap_relabel σ h.2⟩

theorem moveUnchecked_relabel (σ : PieceRelabeling) (s : State)
    (p : Piece) (d : Direction) :
    moveUnchecked (relabelState σ s) (σ.forward p) d =
      (moveUnchecked s p d).map (relabelState σ) := by
  unfold moveUnchecked
  rw [relabel_forward_pos]
  cases translated (s.pos p) d with
  | none => simp
  | some pos =>
      simp
      apply congrArg State.ofFn
      funext q
      rw [State.ofFn_pos]
      by_cases hq : q = σ.forward p
      · subst q
        simp [σ.leftInv]
      · have hinv : σ.inverse q ≠ p := by
          intro heq
          apply hq
          rw [← heq, σ.rightInv]
        simp [hq, hinv]

theorem relabel_inverse_canonical (σ : PieceRelabeling) (f : Piece → Pos) :
    relabelState σ.symm (relabelState σ (State.ofFn f)) = State.ofFn f := by
  apply congrArg State.ofFn
  funext p
  simp only [relabelState_pos, State.ofFn_pos]
  change f (σ.inverse (σ.forward p)) = f p
  rw [σ.leftInv]

theorem relabel_comp (outer inner : PieceRelabeling) (s : State) :
    relabelState outer (relabelState inner s) =
      relabelState (outer.comp inner) s := by
  apply congrArg State.ofFn
  funext p
  simp only [relabelState_pos]
  rfl

theorem moveUnchecked_canonical {s next : State} {p : Piece} {d : Direction}
    (h : moveUnchecked s p d = some next) : State.ofFn next.pos = next := by
  unfold moveUnchecked at h
  cases ht : translated (s.pos p) d with
  | none => simp [ht] at h
  | some pos =>
      simp [ht] at h
      subst next
      apply congrArg State.ofFn
      funext q
      rw [State.ofFn_pos]

theorem valid_relabel_moveCandidate_iff (σ : PieceRelabeling)
    {s next : State} {p : Piece} {d : Direction}
    (hm : moveUnchecked s p d = some next) :
    valid (relabelState σ next) = true ↔ valid next = true := by
  constructor
  · intro h
    have restored := valid_relabel σ.symm h
    have canonical := moveUnchecked_canonical hm
    rw [← canonical, relabel_inverse_canonical] at restored
    simpa only [canonical] using restored
  · exact valid_relabel σ

/-- Relabeling equal-shaped pieces commutes with the executable move function. -/
theorem tryMove_relabel (σ : PieceRelabeling) (s : State)
    (p : Piece) (d : Direction) :
    tryMove (relabelState σ s) (σ.forward p) d =
      (tryMove s p d).map (relabelState σ) := by
  unfold tryMove
  rw [moveUnchecked_relabel]
  cases hm : moveUnchecked s p d with
  | none => simp
  | some next =>
      simp
      by_cases hv : valid next = true
      · have hrv := (valid_relabel_moveCandidate_iff σ hm).mpr hv
        simp [hv, hrv]
      · have hrv : valid (relabelState σ next) ≠ true :=
          fun h => hv ((valid_relabel_moveCandidate_iff σ hm).mp h)
        simp [hv, hrv]

theorem tryMove_unrelabel {σ : PieceRelabeling} {s t : State}
    {p : Piece} {d : Direction}
    (h : tryMove (relabelState σ s) p d = some t) :
    ∃ actual, tryMove s (σ.inverse p) d = some actual ∧
      t = relabelState σ actual := by
  have commute := tryMove_relabel σ s (σ.inverse p) d
  rw [σ.rightInv] at commute
  cases hm : tryMove s (σ.inverse p) d with
  | none =>
      rw [hm, Option.map_none, h] at commute
      contradiction
  | some actual =>
      refine ⟨actual, rfl, ?_⟩
      rw [hm, Option.map_some, h] at commute
      exact Option.some.inj commute

theorem observational_tryMove {s t : State} (h : ObservationalEq s t)
    (p : Piece) (d : Direction) : tryMove s p d = tryMove t p d := by
  unfold tryMove moveUnchecked
  rw [h p]
  cases translated (t.pos p) d with
  | none => simp
  | some pos =>
      simp
      have candidate :
          (State.ofFn fun q => if q = p then pos else s.pos q) =
          State.ofFn fun q => if q = p then pos else t.pos q := by
        apply congrArg State.ofFn
        funext q
        by_cases hqp : q = p
        · simp [hqp]
        · simp [hqp, h q]
      rw [candidate]

theorem observational_goal {s t : State} (h : ObservationalEq s t) :
    goal s = goal t := by
  simp only [goal]
  rw [h .caoCao]

/-- Horizontal reflection of the board. -/
def mirrorPos (p : Piece) (pos : Pos) : Pos :=
  ⟨4 - (pos.x + p.shape.width), pos.y⟩

def mirrorState (s : State) : State :=
  State.ofFn fun p => mirrorPos p (s.pos p)

@[simp] theorem mirrorState_pos (s : State) (p : Piece) :
    (mirrorState s).pos p = mirrorPos p (s.pos p) := by
  simp [mirrorState]

def Direction.mirror : Direction → Direction
  | .up => .up
  | .down => .down
  | .left => .right
  | .right => .left

@[simp] theorem Direction.mirror_mirror (d : Direction) : d.mirror.mirror = d := by
  cases d <;> rfl

def HorizontallyBounded (s : State) : Prop :=
  ∀ p, (s.pos p).x + p.shape.width ≤ 4

theorem mirror_twice (s : State) (h : HorizontallyBounded s) :
    ObservationalEq (mirrorState (mirrorState s)) s := by
  intro p
  have hp := h p
  rcases hpos : s.pos p with ⟨x, y⟩
  simp only [mirrorState_pos, mirrorPos, hpos] at hp ⊢
  congr
  omega

def GoalState (s : State) : Prop := s.pos .caoCao = ⟨1, 3⟩

theorem goal_eq_true_iff (s : State) : goal s = true ↔ GoalState s := by
  exact beq_iff_eq

theorem mirror_goal_iff (s : State) (h : HorizontallyBounded s) :
    GoalState (mirrorState s) ↔ GoalState s := by
  have hc := h .caoCao
  rcases hpos : s.pos .caoCao with ⟨x, y⟩
  simp only [GoalState, mirrorState_pos, mirrorPos, Piece.shape, hpos] at hc ⊢
  constructor
  · intro hg
    have hx := congrArg Pos.x hg
    have hy := congrArg Pos.y hg
    simp only at hx hy
    congr
    omega
  · intro hg
    have hx := congrArg Pos.x hg
    have hy := congrArg Pos.y hg
    simp only at hx hy
    congr
    omega

/-- Every valid state is horizontally bounded, so reflection is involutive on
    every state that can occur during legal play. -/
theorem ValidState.horizontallyBounded {s : State} (h : ValidState s) :
    HorizontallyBounded s := by
  unfold ValidState valid at h
  rw [Bool.and_eq_true] at h
  unfold inBounds at h
  rw [Bool.and_eq_true] at h
  rw [List.all_eq_true] at h
  intro p
  have hp := h.1.2 p p.mem_all
  rw [Bool.and_eq_true] at hp
  exact of_decide_eq_true hp.1

/-- The second quotient used by the overview graph: two nodes agree either
    directly up to equal-shaped labels, or after horizontal reflection. -/
def MirrorEquivalent (s t : State) : Prop :=
  SameShape s t ∨ SameShape (mirrorState s) t

instance (s t : State) : Decidable (MirrorEquivalent s t) := by
  unfold MirrorEquivalent
  infer_instance

theorem mirrorEquivalent_refl (s : State) : MirrorEquivalent s s :=
  Or.inl (sameShape_refl s)

/-- Mirror quotienting cannot change whether a bounded layout is a goal. -/
theorem mirrorEquivalent_goal_iff {s t : State}
    (bounded : HorizontallyBounded s) (h : MirrorEquivalent s t) :
    goal t = true ↔ goal s = true := by
  rcases h with direct | reflected
  · rw [sameShape_goal direct]
  · rw [← sameShape_goal reflected]
    rw [goal_eq_true_iff, goal_eq_true_iff]
    exact mirror_goal_iff s bounded

/-- A quotient transition performs one exact move and then chooses either the
    direct equal-shape class or its horizontal-mirror class. -/
def MirrorQStep (s t : State) : Prop :=
  ∃ p d next, tryMove s p d = some next ∧ MirrorEquivalent next t

theorem qstep_to_mirrorQStep {s t : State} (h : QStep s t) :
    MirrorQStep s t := by
  rcases h with ⟨p, d, next, moved, represented⟩
  exact ⟨p, d, next, moved, Or.inl represented⟩

theorem step_to_mirrorQStep {s t : State} (h : Step s t) :
    MirrorQStep s t :=
  qstep_to_mirrorQStep (step_to_qstep h)

end Huarongdao
