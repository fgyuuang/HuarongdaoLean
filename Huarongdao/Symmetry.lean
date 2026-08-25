import Huarongdao.Paths
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

theorem swapSoldiers12_sameShape (s : State) :
    SameShape (relabelState swapSoldiers12 s) s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact .refl _
  · exact List.Perm.swap _ _ _

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

end Huarongdao
