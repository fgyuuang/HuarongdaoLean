import Huarongdao.ClassicFullSpace
import Mathlib.Data.List.Sublists
import Mathlib.Tactic

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Completeness of the constructive classic-shape enumeration

The executable generator stores equal-shaped pieces in board order.  The
proof below normalizes an arbitrary valid labelled state to that order and
then shows that the normalized placement occurs in `allShapeStatesList`.
-/

/-- Row-major order on board positions. -/
def Pos.boardLE (left right : Pos) : Prop :=
  left.y < right.y ∨ (left.y = right.y ∧ left.x ≤ right.x)

instance : DecidableRel Pos.boardLE := by
  intro left right
  unfold Pos.boardLE
  infer_instance

instance : Std.Antisymm Pos.boardLE where
  antisymm left right leftRight rightLeft := by
    rcases left with ⟨leftX, leftY⟩
    rcases right with ⟨rightX, rightY⟩
    simp only [Pos.boardLE] at leftRight rightLeft
    congr <;> omega

instance : Std.Total Pos.boardLE where
  total left right := by
    rcases left with ⟨leftX, leftY⟩
    rcases right with ⟨rightX, rightY⟩
    simp only [Pos.boardLE]
    omega

instance : IsTrans Pos Pos.boardLE where
  trans left middle right leftMiddle middleRight := by
    rcases left with ⟨leftX, leftY⟩
    rcases middle with ⟨middleX, middleY⟩
    rcases right with ⟨rightX, rightY⟩
    simp only [Pos.boardLE] at leftMiddle middleRight ⊢
    omega

def boardSort (positions : List Pos) : List Pos :=
  positions.mergeSort fun left right => decide (Pos.boardLE left right)

theorem boardSort_perm (positions : List Pos) :
    (boardSort positions).Perm positions := by
  exact List.mergeSort_perm positions _

theorem boardSort_pairwise (positions : List Pos) :
    (boardSort positions).Pairwise Pos.boardLE := by
  simpa [boardSort] using
    (List.pairwise_mergeSort' Pos.boardLE positions)

theorem cao_anchor_mem_of_valid (state : ValidClassicState) :
    state.1.pos .caoCao ∈ caoAnchors := by
  have validState := state.2
  unfold ValidState valid at validState
  rw [Bool.and_eq_true] at validState
  unfold inBounds at validState
  rw [Bool.and_eq_true] at validState
  have bound :=
    List.all_eq_true.mp validState.1.2 .caoCao (Piece.mem_all .caoCao)
  rw [Bool.and_eq_true] at bound
  have xBound : (state.1.pos .caoCao).x + 2 ≤ 4 :=
    of_decide_eq_true bound.1
  have yBound : (state.1.pos .caoCao).y + 2 ≤ 5 :=
    of_decide_eq_true bound.2
  generalize state.1.pos .caoCao = position at xBound yBound ⊢
  rcases position with ⟨x, y⟩
  simp only at xBound yBound
  simp [caoAnchors, anchors, List.mem_flatMap, List.mem_range]
  omega

theorem guan_anchor_mem_of_valid (state : ValidClassicState) :
    state.1.pos .guanYu ∈ guanAnchors := by
  have validState := state.2
  unfold ValidState valid at validState
  rw [Bool.and_eq_true] at validState
  unfold inBounds at validState
  rw [Bool.and_eq_true] at validState
  have bound :=
    List.all_eq_true.mp validState.1.2 .guanYu (Piece.mem_all .guanYu)
  rw [Bool.and_eq_true] at bound
  have xBound : (state.1.pos .guanYu).x + 2 ≤ 4 :=
    of_decide_eq_true bound.1
  have yBound : (state.1.pos .guanYu).y + 1 ≤ 5 :=
    of_decide_eq_true bound.2
  generalize state.1.pos .guanYu = position at xBound yBound ⊢
  rcases position with ⟨x, y⟩
  simp only at xBound yBound
  simp [guanAnchors, anchors, List.mem_flatMap, List.mem_range]
  omega

theorem vertical_anchor_mem_of_valid
    (state : ValidClassicState) (piece : Piece)
    (shape : piece.shape = ⟨1, 2⟩) :
    state.1.pos piece ∈ verticalAnchors := by
  have validState := state.2
  unfold ValidState valid at validState
  rw [Bool.and_eq_true] at validState
  unfold inBounds at validState
  rw [Bool.and_eq_true] at validState
  have bound :=
    List.all_eq_true.mp validState.1.2 piece (Piece.mem_all piece)
  rw [Bool.and_eq_true] at bound
  rw [shape] at bound
  have xBound : (state.1.pos piece).x + 1 ≤ 4 :=
    of_decide_eq_true bound.1
  have yBound : (state.1.pos piece).y + 2 ≤ 5 :=
    of_decide_eq_true bound.2
  generalize state.1.pos piece = position at xBound yBound ⊢
  rcases position with ⟨x, y⟩
  simp only at xBound yBound
  simp [verticalAnchors, anchors, List.mem_flatMap, List.mem_range]
  omega

theorem soldier_anchor_mem_board_of_valid
    (state : ValidClassicState) (piece : Piece)
    (shape : piece.shape = ⟨1, 1⟩) :
    state.1.pos piece ∈ boardCells := by
  have validState := state.2
  unfold ValidState valid at validState
  rw [Bool.and_eq_true] at validState
  unfold inBounds at validState
  rw [Bool.and_eq_true] at validState
  have bound :=
    List.all_eq_true.mp validState.1.2 piece (Piece.mem_all piece)
  rw [Bool.and_eq_true] at bound
  rw [shape] at bound
  have xBound : (state.1.pos piece).x + 1 ≤ 4 :=
    of_decide_eq_true bound.1
  have yBound : (state.1.pos piece).y + 1 ≤ 5 :=
    of_decide_eq_true bound.2
  generalize state.1.pos piece = position at xBound yBound ⊢
  rcases position with ⟨x, y⟩
  simp only at xBound yBound
  simp [boardCells, anchors, List.mem_flatMap, List.mem_range]
  omega

def normalizedVerticalPositions (state : State) : List Pos :=
  boardSort (verticalPositions state)

def normalizedSoldierPositions (state : State) : List Pos :=
  boardSort (soldierPositions state)

theorem normalizedVerticalPositions_perm (state : State) :
    (normalizedVerticalPositions state).Perm (verticalPositions state) :=
  boardSort_perm _

theorem normalizedSoldierPositions_perm (state : State) :
    (normalizedSoldierPositions state).Perm (soldierPositions state) :=
  boardSort_perm _

theorem vertical_positions_nodup (state : ValidClassicState) :
    (verticalPositions state.1).Nodup := by
  have piecesNodup :
      ([Piece.zhangFei, .zhaoYun, .maChao, .huangZhong] : List Piece).Nodup := by
    decide
  exact piecesNodup.map (valid_pos_injective state.2)

theorem soldier_positions_nodup (state : ValidClassicState) :
    (soldierPositions state.1).Nodup := by
  have piecesNodup :
      ([Piece.soldier1, .soldier2, .soldier3, .soldier4] : List Piece).Nodup := by
    decide
  exact piecesNodup.map (valid_pos_injective state.2)

theorem normalized_vertical_mem_sublists (state : ValidClassicState) :
    normalizedVerticalPositions state.1 ∈ verticalAnchors.sublistsLen 4 := by
  rw [List.mem_sublistsLen]
  constructor
  · apply List.sublist_of_subperm_of_pairwise (r := Pos.boardLE)
    · apply
        (normalizedVerticalPositions_perm state.1).subperm.trans
      apply List.subperm_of_subset
      · exact vertical_positions_nodup state
      intro position member
      simp only [verticalPositions, List.mem_map] at member
      rcases member with ⟨piece, pieceMem, rfl⟩
      simp only [List.mem_cons] at pieceMem
      rcases pieceMem with rfl | rfl | rfl | rfl | pieceMem
      · exact vertical_anchor_mem_of_valid state .zhangFei rfl
      · exact vertical_anchor_mem_of_valid state .zhaoYun rfl
      · exact vertical_anchor_mem_of_valid state .maChao rfl
      · exact vertical_anchor_mem_of_valid state .huangZhong rfl
      · contradiction
    · exact boardSort_pairwise _
    · native_decide
  · simpa [normalizedVerticalPositions, boardSort, verticalPositions] using
      List.Perm.length_eq (normalizedVerticalPositions_perm state.1)

def largePieces : List Piece :=
  [.caoCao, .guanYu, .zhangFei, .zhaoYun, .maChao, .huangZhong]

def largeOccupiedCells (state : State) : List Pos :=
  largePieces.flatMap (occupiedCells state)

theorem occupiedCells_nodup (state : State) (piece : Piece) :
    (occupiedCells state piece).Nodup := by
  rcases positionEq : state.pos piece with ⟨x, y⟩
  cases piece <;>
    norm_num [occupiedCells, Piece.shape, positionEq, List.range_succ,
      List.nodup_cons, Pos.mk.injEq]

theorem occupiedCells_disjoint_of_valid
    (state : ValidClassicState) {left right : Piece}
    (different : left ≠ right) :
    (occupiedCells state.1 left).Disjoint
      (occupiedCells state.1 right) := by
  rw [List.disjoint_left]
  intro cell leftMember rightMember
  have validState := state.2
  unfold ValidState valid at validState
  rw [Bool.and_eq_true] at validState
  have pairClear :=
    List.all_eq_true.mp
      (List.all_eq_true.mp validState.2 left (Piece.mem_all left))
      right (Piece.mem_all right)
  rw [Piece.beq_eq_false_of_ne different] at pairClear
  simp only [Bool.false_or] at pairClear
  have unequal :=
    List.all_eq_true.mp
      (List.all_eq_true.mp pairClear cell leftMember)
      cell rightMember
  exact (bne_iff_ne.mp unequal) rfl

theorem largePieces_nodup : largePieces.Nodup := by
  native_decide

theorem largeOccupiedCells_nodup (state : ValidClassicState) :
    (largeOccupiedCells state.1).Nodup := by
  rw [largeOccupiedCells, List.nodup_flatMap]
  constructor
  · intro piece _
    exact occupiedCells_nodup state.1 piece
  · apply List.Pairwise.imp
      (fun different =>
        occupiedCells_disjoint_of_valid state different)
    exact largePieces_nodup

theorem rectangleCells_eq_occupiedCells
    (state : State) (piece : Piece) :
    rectangleCells (state.pos piece) piece.shape =
      occupiedCells state piece := by
  rfl

def normalizedLargeOccupiedCells (state : State) : List Pos :=
  rectangleCells (state.pos .caoCao) ⟨2, 2⟩ ++
  rectangleCells (state.pos .guanYu) ⟨2, 1⟩ ++
  (normalizedVerticalPositions state).flatMap fun anchor =>
    rectangleCells anchor ⟨1, 2⟩

theorem normalizedLargeOccupiedCells_perm (state : State) :
    (normalizedLargeOccupiedCells state).Perm
      (largeOccupiedCells state) := by
  unfold normalizedLargeOccupiedCells largeOccupiedCells largePieces
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.append_assoc]
  apply List.Perm.append
  · exact List.Perm.of_eq
      (rectangleCells_eq_occupiedCells state .caoCao)
  · apply List.Perm.append
    · exact List.Perm.of_eq
        (rectangleCells_eq_occupiedCells state .guanYu)
    · have verticalPerm :=
        (normalizedVerticalPositions_perm state).flatMap
          (f := fun anchor => rectangleCells anchor ⟨1, 2⟩)
          (g := fun anchor => rectangleCells anchor ⟨1, 2⟩)
          (fun _ _ => List.Perm.refl _)
      simp only [verticalPositions, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] at verticalPerm
      have hZ :
          rectangleCells (state.pos .zhangFei) ⟨1, 2⟩ =
            occupiedCells state .zhangFei := by
        simpa [Piece.shape] using
          (rectangleCells_eq_occupiedCells state .zhangFei)
      have hY :
          rectangleCells (state.pos .zhaoYun) ⟨1, 2⟩ =
            occupiedCells state .zhaoYun := by
        simpa [Piece.shape] using
          (rectangleCells_eq_occupiedCells state .zhaoYun)
      have hM :
          rectangleCells (state.pos .maChao) ⟨1, 2⟩ =
            occupiedCells state .maChao := by
        simpa [Piece.shape] using
          (rectangleCells_eq_occupiedCells state .maChao)
      have hH :
          rectangleCells (state.pos .huangZhong) ⟨1, 2⟩ =
            occupiedCells state .huangZhong := by
        simpa [Piece.shape] using
          (rectangleCells_eq_occupiedCells state .huangZhong)
      rw [hZ, hY, hM, hH] at verticalPerm
      exact verticalPerm

theorem normalizedLargeOccupiedCells_nodup
    (state : ValidClassicState) :
    (normalizedLargeOccupiedCells state.1).Nodup := by
  exact
    (normalizedLargeOccupiedCells_perm state.1).nodup_iff.mpr
      (largeOccupiedCells_nodup state)

theorem soldier_position_not_mem_largeOccupiedCells
    (state : ValidClassicState) {soldier : Piece}
    (soldierShape : soldier.shape = ⟨1, 1⟩)
    {cell : Pos} (cellEq : state.1.pos soldier = cell) :
    cell ∉ largeOccupiedCells state.1 := by
  intro member
  simp only [largeOccupiedCells, List.mem_flatMap] at member
  rcases member with ⟨large, largeMember, cellMember⟩
  have different : soldier ≠ large := by
    intro equal
    subst large
    simp only [largePieces, List.mem_cons] at largeMember
    rcases largeMember with rfl | rfl | rfl | rfl | rfl | rfl | contradiction
    all_goals simp [Piece.shape] at soldierShape
    simp at contradiction
  have disjoint :=
    occupiedCells_disjoint_of_valid state different
  rw [List.disjoint_left] at disjoint
  apply disjoint (origin_mem_occupiedCells state.1 soldier)
  rw [cellEq]
  exact cellMember

theorem normalized_soldier_subset_free
    (state : ValidClassicState) :
    ∀ cell ∈ normalizedSoldierPositions state.1,
      cell ∈
        boardCells.filter fun candidate =>
          candidate ∉ normalizedLargeOccupiedCells state.1 := by
  intro cell member
  have sourceMember :
      cell ∈ soldierPositions state.1 :=
    (normalizedSoldierPositions_perm state.1).mem_iff.mp member
  simp only [soldierPositions, List.mem_map] at sourceMember
  rcases sourceMember with ⟨soldier, soldierMember, cellEq⟩
  have soldierShape : soldier.shape = ⟨1, 1⟩ := by
    simp only [List.mem_cons] at soldierMember
    rcases soldierMember with rfl | rfl | rfl | rfl | contradiction
    · rfl
    · rfl
    · rfl
    · rfl
    · simp at contradiction
  have boardMember : cell ∈ boardCells := by
    rw [← cellEq]
    exact soldier_anchor_mem_board_of_valid state soldier soldierShape
  rw [List.mem_filter]
  refine ⟨boardMember, ?_⟩
  simp only [decide_eq_true_eq]
  intro occupiedMember
  have sourceOccupied :
      cell ∈ largeOccupiedCells state.1 :=
    (normalizedLargeOccupiedCells_perm state.1).mem_iff.mp occupiedMember
  apply
    soldier_position_not_mem_largeOccupiedCells
      state (soldier := soldier) (cell := cell)
  · exact soldierShape
  · exact cellEq
  · exact sourceOccupied

theorem filtered_board_pairwise
    (occupied : List Pos) :
    (boardCells.filter fun cell => cell ∉ occupied).Pairwise Pos.boardLE := by
  exact
    (by native_decide : boardCells.Pairwise Pos.boardLE).sublist
      List.filter_sublist

theorem normalized_soldier_mem_sublists
    (state : ValidClassicState) :
    normalizedSoldierPositions state.1 ∈
      (boardCells.filter fun cell =>
        cell ∉ normalizedLargeOccupiedCells state.1).sublistsLen 4 := by
  rw [List.mem_sublistsLen]
  constructor
  · apply List.sublist_of_subperm_of_pairwise (r := Pos.boardLE)
    · apply List.subperm_of_subset
      · exact
          (normalizedSoldierPositions_perm state.1).nodup_iff.mpr
            (soldier_positions_nodup state)
      · exact normalized_soldier_subset_free state
    · exact boardSort_pairwise _
    · exact filtered_board_pairwise _
  · simpa [normalizedSoldierPositions, boardSort, soldierPositions] using
      List.Perm.length_eq (normalizedSoldierPositions_perm state.1)

end ClassicFullSpace
end Huarongdao
