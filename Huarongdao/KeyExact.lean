import Huarongdao.Symmetry
import Std.Tactic

namespace Huarongdao

/-- Lexicographic order on board positions, used to canonicalize unlabeled
    piece lists without relying on the numeric cell code. -/
def Pos.leProp (a b : Pos) : Prop :=
  a.x < b.x ∨ (a.x = b.x ∧ a.y ≤ b.y)

instance (a b : Pos) : Decidable (Pos.leProp a b) := by
  unfold Pos.leProp
  infer_instance

def Pos.le (a b : Pos) : Bool := decide (Pos.leProp a b)

theorem pos_le_trans {a b c : Pos} (h1 : Pos.leProp a b) (h2 : Pos.leProp b c) :
    Pos.leProp a c := by
  rcases h1 with h1x | ⟨h1x, h1y⟩ <;> rcases h2 with h2x | ⟨h2x, h2y⟩
  · left; omega
  · left; omega
  · left; omega
  · right; constructor <;> omega

theorem pos_le_total (a b : Pos) : Pos.le a b = true ∨ Pos.le b a = true := by
  unfold Pos.le
  by_cases h1 : Pos.leProp a b
  · left; simp [h1]
  · right
    cases a with | mk ax ay =>
    cases b with | mk bx bY =>
    dsimp [Pos.leProp] at h1
    rw [decide_eq_true_eq]
    dsimp [Pos.leProp]
    by_cases hx : ax = bx
    · right; constructor; exact hx.symm; omega
    · left; omega

theorem pos_le_total_comp (a b : Pos) : (Pos.le a b || Pos.le b a) = true := by
  have h := pos_le_total a b
  rcases h with h | h <;> simp [h]

theorem pos_le_antisymm {a b : Pos} (h1 : Pos.leProp a b) (h2 : Pos.leProp b a) :
    a = b := by
  cases a with | mk ax ay =>
  cases b with | mk bx bY =>
  dsimp [Pos.leProp] at h1 h2
  rcases h1 with h1x | ⟨h1x, h1y⟩ <;> rcases h2 with h2x | ⟨h2x, h2y⟩
  · omega
  · omega
  · omega
  · subst h1x
    congr
    omega

/-- The sorted canonical form of a list of positions. -/
def sortedPosList (ps : List Pos) : List Pos :=
  ps.mergeSort Pos.le

theorem pairwise_pos_mergeSort (l : List Pos) :
    List.Pairwise (fun a b : Pos => Pos.leProp a b) (sortedPosList l) := by
  have sorted := List.pairwise_mergeSort
    (le := Pos.le)
    (fun a b c hab hbc => by
      simp only [Pos.le, decide_eq_true_eq] at hab hbc ⊢
      exact pos_le_trans hab hbc)
    (fun a b => pos_le_total_comp a b)
    l
  simpa only [Pos.le, decide_eq_true_eq, sortedPosList] using sorted

theorem sorted_unique_pos {left right : List Pos}
    (leftSorted : List.Pairwise (fun a b : Pos => Pos.leProp a b) left)
    (rightSorted : List.Pairwise (fun a b : Pos => Pos.leProp a b) right)
    (perm : left.Perm right) : left = right := by
  apply List.Perm.eq_of_pairwise (le := fun a b : Pos => Pos.leProp a b)
  · intro a b _ _ hab hba
    exact pos_le_antisymm hab hba
  · exact leftSorted
  · exact rightSorted
  · exact perm

theorem mergeSort_perm (l : List Pos) : (sortedPosList l).Perm l := by
  simpa [sortedPosList] using List.mergeSort_perm l Pos.le

theorem sortedPosList_eq_of_perm {l m : List Pos} (h : l.Perm m) :
    sortedPosList l = sortedPosList m := by
  apply sorted_unique_pos
  · exact pairwise_pos_mergeSort l
  · exact pairwise_pos_mergeSort m
  · exact (mergeSort_perm l).trans (h.trans (mergeSort_perm m).symm)

theorem perm_of_sortedPosList_eq {l m : List Pos} (h : sortedPosList l = sortedPosList m) :
    l.Perm m := by
  have hperm : (sortedPosList l).Perm m := h ▸ mergeSort_perm m
  exact (mergeSort_perm l).symm.trans hperm

/-- The sorted numeric-code list used by the executable string key. -/
def sortedNatList (l : List Nat) : List Nat := l.mergeSort

theorem pairwise_nat_mergeSort (l : List Nat) :
    List.Pairwise (fun a b : Nat => a ≤ b) (sortedNatList l) := by
  have sorted := List.pairwise_mergeSort
    (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      omega)
    (fun a b => by
      by_cases h : a ≤ b
      · simp [h]
      · have h' : b ≤ a := by omega
        simp [h, h'])
    l
  simpa only [decide_eq_true_eq, sortedNatList] using sorted

theorem sorted_unique_nat {left right : List Nat}
    (leftSorted : List.Pairwise (fun a b : Nat => a ≤ b) left)
    (rightSorted : List.Pairwise (fun a b : Nat => a ≤ b) right)
    (perm : left.Perm right) : left = right := by
  apply List.Perm.eq_of_pairwise (le := fun a b : Nat => a ≤ b)
  · intro a b _ _ hab hba
    omega
  · exact leftSorted
  · exact rightSorted
  · exact perm

theorem sortedNatList_perm (l : List Nat) : (sortedNatList l).Perm l := by
  simpa [sortedNatList] using
    List.mergeSort_perm l (fun a b => decide (a ≤ b))

theorem sortedNatList_eq_of_perm {l m : List Nat} (h : l.Perm m) :
    sortedNatList l = sortedNatList m := by
  apply sorted_unique_nat
  · exact pairwise_nat_mergeSort l
  · exact pairwise_nat_mergeSort m
  · exact (sortedNatList_perm l).trans (h.trans (sortedNatList_perm m).symm)

theorem codesKey_eq_of_perm {l m : List Nat} (h : l.Perm m) :
    codesKey l = codesKey m := by
  unfold codesKey
  change ",".intercalate ((sortedNatList l).map toString) =
    ",".intercalate ((sortedNatList m).map toString)
  rw [sortedNatList_eq_of_perm h]

/-- The executable string key is sound for the equal-shape quotient:
    equal-shape states always receive the same canonical key. -/
theorem sameShape_stateKey_eq {s t : State} (h : SameShape s t) :
    State.key s = State.key t := by
  rcases h with ⟨hcao, hguan, hvert, hsold⟩
  have hvertCodes :
      ([.zhangFei, .zhaoYun, .maChao, .huangZhong].map fun p =>
        (s.pos p).code).Perm
        ([.zhangFei, .zhaoYun, .maChao, .huangZhong].map fun p =>
          (t.pos p).code) := by
    simpa [verticalPositions] using hvert.map Pos.code
  have hsoldCodes :
      ([.soldier1, .soldier2, .soldier3, .soldier4].map fun p =>
        (s.pos p).code).Perm
        ([.soldier1, .soldier2, .soldier3, .soldier4].map fun p =>
          (t.pos p).code) := by
    simpa [soldierPositions] using hsold.map Pos.code
  simp only [State.key]
  rw [hcao, hguan,
    codesKey_eq_of_perm hvertCodes, codesKey_eq_of_perm hsoldCodes]

namespace State

/-- Typed canonical representative of a state in the equal-shape quotient.
    Keeping positions as `Pos` makes the exact correspondence with `SameShape`
    independent of the numeric cell-code encoding used by the string key. -/
structure KeyParts where
  cao : Pos
  guan : Pos
  vertical : List Pos
  soldiers : List Pos
  deriving DecidableEq, Repr

theorem KeyParts.ext {a b : KeyParts}
    (hcao : a.cao = b.cao) (hguan : a.guan = b.guan)
    (hvert : a.vertical = b.vertical) (hsold : a.soldiers = b.soldiers) :
    a = b := by
  cases a; cases b
  simp_all

/-- Canonical sorted representation of the equal-shape state class. -/
def keyParts (s : State) : State.KeyParts where
  cao := s.pos .caoCao
  guan := s.pos .guanYu
  vertical := sortedPosList (verticalPositions s)
  soldiers := sortedPosList (soldierPositions s)

/-- `keyParts` is a complete invariant for the equal-shape quotient: it
    identifies exactly the states that are equal after forgetting the labels
    of equal-shaped pieces. -/
theorem keyParts_eq_iff_sameShape (s t : State) :
    State.keyParts s = State.keyParts t ↔ SameShape s t := by
  constructor
  · intro h
    exact ⟨congrArg State.KeyParts.cao h, congrArg State.KeyParts.guan h,
      perm_of_sortedPosList_eq (congrArg State.KeyParts.vertical h),
      perm_of_sortedPosList_eq (congrArg State.KeyParts.soldiers h)⟩
  · intro h
    rcases h with ⟨hcao, hguan, hvert, hsold⟩
    apply State.KeyParts.ext
    · exact hcao
    · exact hguan
    · exact sortedPosList_eq_of_perm hvert
    · exact sortedPosList_eq_of_perm hsold

end State

end Huarongdao
