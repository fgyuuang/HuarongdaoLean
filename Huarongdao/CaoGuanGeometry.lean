import Huarongdao.CaoProjection
import Huarongdao.StateSpaceConnectivity
import Huarongdao.Bottleneck
import Huarongdao.ClassicSolution
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Huarongdao
namespace CaoGuanGeometry

/-!
This file separates geometric observations from the full labelled state.

`CaoPosition` and `GuanYuPosition` use `Fin` coordinates.  The first
coordinate is the column of the top-left corner and the second coordinate is
the row.  Thus the types are definitionally finite, while the validity proof
is what justifies turning a raw `Pos` into one of these bounded coordinates.
-/

abbrev CaoPosition := Fin 3 × Fin 4
abbrev GuanYuPosition := Fin 3 × Fin 5

theorem caoPosition_card : Fintype.card CaoPosition = 12 := by
  native_decide

theorem guanYuPosition_card : Fintype.card GuanYuPosition = 15 := by
  native_decide

def CaoPosition.toPos (position : CaoPosition) : Pos :=
  ⟨position.1.val, position.2.val⟩

def GuanYuPosition.toPos (position : GuanYuPosition) : Pos :=
  ⟨position.1.val, position.2.val⟩

private theorem cao_x_lt_three (state : ValidClassicState) :
    (state.1.pos .caoCao).x < 3 := by
  have bound := valid_horizontallyBounded state.2 .caoCao
  change (state.1.pos .caoCao).x + 2 ≤ 4 at bound
  omega

private theorem cao_y_lt_four (state : ValidClassicState) :
    (state.1.pos .caoCao).y < 4 := by
  have validState := state.2
  unfold ValidState valid at validState
  rw [Bool.and_eq_true] at validState
  rcases validState with ⟨bounds, _⟩
  unfold inBounds at bounds
  rw [Bool.and_eq_true] at bounds
  rcases bounds with ⟨_, allBounds⟩
  have pieceBound :=
    (List.all_eq_true.mp allBounds) .caoCao (Piece.mem_all .caoCao)
  rw [Bool.and_eq_true] at pieceBound
  have heightBound : (state.1.pos .caoCao).y + 2 ≤ 5 :=
    of_decide_eq_true pieceBound.2
  omega

private theorem guan_x_lt_three (state : ValidClassicState) :
    (state.1.pos .guanYu).x < 3 := by
  have bound := valid_horizontallyBounded state.2 .guanYu
  change (state.1.pos .guanYu).x + 2 ≤ 4 at bound
  omega

private theorem guan_y_lt_five (state : ValidClassicState) :
    (state.1.pos .guanYu).y < 5 := by
  have validState := state.2
  unfold ValidState valid at validState
  rw [Bool.and_eq_true] at validState
  rcases validState with ⟨bounds, _⟩
  unfold inBounds at bounds
  rw [Bool.and_eq_true] at bounds
  rcases bounds with ⟨_, allBounds⟩
  have pieceBound :=
    (List.all_eq_true.mp allBounds) .guanYu (Piece.mem_all .guanYu)
  rw [Bool.and_eq_true] at pieceBound
  have heightBound : (state.1.pos .guanYu).y + 1 ≤ 5 :=
    of_decide_eq_true pieceBound.2
  omega

/-- The strict Cao Cao top-left observation. -/
def caoPositionObservation (state : ValidClassicState) : CaoPosition :=
  let position := state.1.pos .caoCao
  ⟨⟨position.x, cao_x_lt_three state⟩, ⟨position.y, cao_y_lt_four state⟩⟩

/-- The strict Guan Yu top-left observation. -/
def guanYuPositionObservation (state : ValidClassicState) : GuanYuPosition :=
  let position := state.1.pos .guanYu
  ⟨⟨position.x, guan_x_lt_three state⟩, ⟨position.y, guan_y_lt_five state⟩⟩

/-- Names matching the mathematical notation `π_C` and `π_G`. -/
abbrev pi_C := caoPositionObservation

abbrev pi_G := guanYuPositionObservation

/-- The joint observation of the two distinguished pieces. -/
def jointObservation (state : ValidClassicState) :
    CaoPosition × GuanYuPosition :=
  (caoPositionObservation state, guanYuPositionObservation state)

@[simp] theorem caoPositionObservation_toPos (state : ValidClassicState) :
    (caoPositionObservation state).toPos =
      state.1.pos .caoCao := by
  rfl

@[simp] theorem guanYuPositionObservation_toPos (state : ValidClassicState) :
    (guanYuPositionObservation state).toPos =
      state.1.pos .guanYu := by
  rfl

/-- The fibre of the strict Cao Cao observation. -/
def caoFiber (position : CaoPosition) : Set ValidClassicState :=
  {state | caoPositionObservation state = position}

/-- The fibre of the strict Guan Yu observation. -/
def guanYuFiber (position : GuanYuPosition) : Set ValidClassicState :=
  {state | guanYuPositionObservation state = position}

/-- Joint fibres can be used when both distinguished pieces are fixed. -/
def jointFiber (position : CaoPosition × GuanYuPosition) :
    Set ValidClassicState :=
  {state | jointObservation state = position}

@[simp] theorem mem_caoFiber_iff
    (state : ValidClassicState) (position : CaoPosition) :
    state ∈ caoFiber position ↔
      caoPositionObservation state = position :=
  Iff.rfl

@[simp] theorem mem_guanYuFiber_iff
    (state : ValidClassicState) (position : GuanYuPosition) :
    state ∈ guanYuFiber position ↔
      guanYuPositionObservation state = position :=
  Iff.rfl

@[simp] theorem mem_jointFiber_iff
    (state : ValidClassicState)
    (position : CaoPosition × GuanYuPosition) :
    state ∈ jointFiber position ↔ jointObservation state = position :=
  Iff.rfl

/-- A raw coordinate Manhattan distance. -/
def coordinateManhattan (left right : Pos) : Nat :=
  (if left.x ≤ right.x then right.x - left.x else left.x - right.x) +
    (if left.y ≤ right.y then right.y - left.y else left.y - right.y)

/-- Manhattan distance on the 12-point Cao Cao position space. -/
def caoCoordinateManhattan (left right : CaoPosition) : Nat :=
  coordinateManhattan left.toPos right.toPos

/-- Manhattan distance on the 15-point Guan Yu position space. -/
def guanYuCoordinateManhattan (left right : GuanYuPosition) : Nat :=
  coordinateManhattan left.toPos right.toPos

def caoCoordinateAdjacent (left right : CaoPosition) : Prop :=
  caoCoordinateManhattan left right = 1

def concreteStateGraph : SimpleGraph ValidClassicState :=
  ClassicStateSpaceKernel.concrete.simpleGraph
    ClassicStateSpaceKernel.concreteReversible

/-- The exact fixed-Cao-position graph `G[F_p]`. -/
def fixedCaoGraph (position : CaoPosition) : SimpleGraph
    {state : ValidClassicState // state ∈ caoFiber position} :=
  concreteStateGraph.induce (caoFiber position)

/-- Connected components of a fixed-Cao-position graph. -/
abbrev FixedCaoComponent (position : CaoPosition) :=
  (fixedCaoGraph position).ConnectedComponent

/-- The existential position graph induced by concrete legal edges. -/
def caoPositionGraph : SimpleGraph CaoPosition where
  Adj left right :=
    left ≠ right ∧
      ∃ source target,
        source ∈ caoFiber left ∧
        target ∈ caoFiber right ∧
        concreteStateGraph.Adj source target
  symm := ⟨by
    intro left right adjacent
    rcases adjacent with
      ⟨different, source, target, sourceMem, targetMem, adjacent⟩
    exact ⟨different.symm, target, source, targetMem, sourceMem, adjacent.symm⟩⟩
  loopless := ⟨by
    intro position adjacent
    exact adjacent.1 rfl⟩

/-- Extended distance in the existential Cao-position graph. -/
noncomputable def caoPositionGraphEdist
    (left right : CaoPosition) : ℕ∞ :=
  caoPositionGraph.edist left right

/-- The natural-number view of the position graph distance. -/
noncomputable def caoPositionGraphDist
    (left right : CaoPosition) : Nat :=
  caoPositionGraph.dist left right

/-- Extended shortest distance in the concrete state graph. -/
noncomputable def concreteStateGraphEdist
    (source target : ValidClassicState) : ℕ∞ :=
  concreteStateGraph.edist source target

/-- The natural-number concrete graph distance.  It is intended for connected
    pairs; `concreteStateGraphEdist` retains `⊤` for disconnected pairs. -/
noncomputable def concreteStateGraphDist
    (source target : ValidClassicState) : Nat :=
  concreteStateGraph.dist source target

/-- The minimum extended distance between two Cao fibres. -/
noncomputable def caoFiberMinEdist
    (left right : CaoPosition) : ℕ∞ :=
  ⨅ source : {state : ValidClassicState // state ∈ caoFiber left},
    ⨅ target : {state : ValidClassicState // state ∈ caoFiber right},
      concreteStateGraphEdist source.1 target.1

/-- Directed Hausdorff distance from one Cao fibre to another. -/
noncomputable def caoFiberDirectedHausdorff
    (left right : CaoPosition) : ℕ∞ :=
  ⨆ source : {state : ValidClassicState // state ∈ caoFiber left},
    ⨅ target : {state : ValidClassicState // state ∈ caoFiber right},
      concreteStateGraphEdist source.1 target.1

/-- Symmetric Hausdorff distance between Cao fibres. -/
noncomputable def caoFiberHausdorff
    (left right : CaoPosition) : ℕ∞ :=
  max (caoFiberDirectedHausdorff left right)
    (caoFiberDirectedHausdorff right left)

/-- A state-dependent one-step observation relation.  This is different from
the existential position graph: the source state is fixed here. -/
def oneStepCaoPosition
    (source : ValidClassicState) (targetPosition : CaoPosition) : Prop :=
  ∃ action target,
    ClassicStateSpaceKernel.concrete.step source action target ∧
      caoPositionObservation target = targetPosition

theorem caoPosition_eq_of_step_other
    {source target : ValidClassicState} {action : Action}
    (step : ClassicStateSpaceKernel.concrete.step source action target)
    (other : action.piece ≠ .caoCao) :
    caoPositionObservation source = caoPositionObservation target := by
  have rawEqual :=
    ClassicStateSpaceKernel.caoPosition_eq_of_step_other step other
  change source.1.pos .caoCao = target.1.pos .caoCao at rawEqual
  apply Prod.ext
  · apply Fin.ext
    change (source.1.pos .caoCao).x = (target.1.pos .caoCao).x
    exact congrArg Pos.x rawEqual
  · apply Fin.ext
    change (source.1.pos .caoCao).y = (target.1.pos .caoCao).y
    exact congrArg Pos.y rawEqual

theorem caoPositionGraph_adj_of_step
    {source target : ValidClassicState} {action : Action}
    (step : ClassicStateSpaceKernel.concrete.step source action target)
    (changes : caoPositionObservation source ≠
      caoPositionObservation target) :
    caoPositionGraph.Adj
      (caoPositionObservation source) (caoPositionObservation target) := by
  have stateDifferent : source ≠ target := by
    intro equal
    apply changes
    simp [equal]
  exact ⟨changes, source, target, rfl, rfl, ⟨⟨action, step⟩, stateDifferent⟩⟩

theorem oneStepCaoPosition_of_other_piece
    {source target : ValidClassicState} {action : Action}
    (step : ClassicStateSpaceKernel.concrete.step source action target)
    (other : action.piece ≠ .caoCao) :
  oneStepCaoPosition source (caoPositionObservation source) := by
  exact ⟨action, target, step, (caoPosition_eq_of_step_other step other).symm⟩

/-- A piece is movable inside a fixed Cao fibre when one of its legal moves
leaves Cao Cao's observation unchanged. -/
def movablePieceWithinCaoFiber
    (state : ValidClassicState) (piece : Piece) : Prop :=
  ∃ direction target,
    ClassicStateSpaceKernel.concrete.step
      state ⟨piece, direction⟩ target ∧
      caoPositionObservation target = caoPositionObservation state

theorem movablePieceWithinCaoFiber_of_other_piece_step
    {source target : ValidClassicState} {action : Action}
    (step : ClassicStateSpaceKernel.concrete.step source action target)
    (other : action.piece ≠ .caoCao) :
    movablePieceWithinCaoFiber source action.piece := by
  exact ⟨action.direction, target, step,
    (caoPosition_eq_of_step_other step other).symm⟩

def classicValid : ValidClassicState :=
  ⟨classic, classic_valid⟩

def classicCaoDownPosition : CaoPosition :=
  ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

theorem classic_cao_position_adjacent :
    caoCoordinateAdjacent
      (caoPositionObservation classicValid) classicCaoDownPosition := by
  change caoCoordinateManhattan
      (caoPositionObservation classicValid) classicCaoDownPosition = 1
  native_decide

theorem classic_cao_down_is_illegal :
    tryMove classic .caoCao .down = none := by
  native_decide

private theorem classic_cao_tryMove_none (direction : Direction) :
    tryMove classic .caoCao direction = none := by
  cases direction <;> native_decide

/-- This is the precise counterexample to the implication
`Manhattan distance one -> legal one-step move`: in `classic`, the position
directly below Cao Cao is adjacent in coordinates, but Guan Yu occupies the
new bottom row of the translated 2-by-2 block. -/
theorem classic_has_no_one_step_to_adjacent_cao_position :
    ¬ oneStepCaoPosition classicValid classicCaoDownPosition := by
  intro witness
  rcases witness with ⟨action, target, step, targetPosition⟩
  have sourcePosition :
      caoPositionObservation classicValid =
        ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ := by
    native_decide
  have changed :
      caoPositionObservation classicValid ≠
        caoPositionObservation target := by
    rw [targetPosition]
    native_decide
  have actionIsCao :
      action.piece = .caoCao :=
    ClassicStateSpaceKernel.action_eq_caoCao_of_caoPosition_ne
      step (by
        intro rawEqual
        apply changed
        change classicValid.1.pos .caoCao = target.1.pos .caoCao at rawEqual
        apply Prod.ext <;> apply Fin.ext
        · simpa [caoPositionObservation] using
            congrArg (fun position : Pos => position.x) rawEqual
        · simpa [caoPositionObservation] using
            congrArg (fun position : Pos => position.y) rawEqual)
  rcases action with ⟨piece, direction⟩
  simp only at actionIsCao
  cases actionIsCao
  have impossible :
      tryMove classic .caoCao direction = none :=
    classic_cao_tryMove_none direction
  change tryMove classic .caoCao direction = some target.1 at step
  rw [impossible] at step
  simp at step

/-- Projection of a set of legal states to the Cao position space. -/
def projectCao (states : Set ValidClassicState) : Set CaoPosition :=
  caoPositionObservation '' states

/-- Projection of a set of legal states to the Guan Yu position space. -/
def projectGuanYu (states : Set ValidClassicState) : Set GuanYuPosition :=
  guanYuPositionObservation '' states

/-- Joint projection retaining both distinguished positions. -/
def projectJoint (states : Set ValidClassicState) :
    Set (CaoPosition × GuanYuPosition) :=
  jointObservation '' states

end CaoGuanGeometry

end Huarongdao

namespace Huarongdao

/--
The geometric reading of "Cao Cao is below Guan Yu": Cao Cao starts on a
strictly lower row, and the two rectangular pieces have overlapping horizontal
projections.  The board convention has `y = 0` at the top, so larger `y` means
lower on the board.
-/
def CaoBelowGuanYu (state : State) : Prop :=
  let cao := state.pos .caoCao
  let guan := state.pos .guanYu
  guan.y < cao.y ∧
    guan.x < cao.x + 2 ∧
    cao.x < guan.x + 2

theorem valid_goal_caoBelowGuanYu {state : State}
    (validState : ValidState state) (goalState : goal state = true) :
    CaoBelowGuanYu state := by
  have hvalid : inBounds state = true ∧ noOverlap state = true := by
    simpa [ValidState, valid] using validState
  have hcao : state.pos .caoCao = ⟨1, 3⟩ :=
    (goal_eq_true_iff state).mp goalState
  have hboundAll := hvalid.1
  unfold inBounds at hboundAll
  rw [Bool.and_eq_true] at hboundAll
  have hguanBounds :=
    (List.all_eq_true.mp hboundAll.2)
      Piece.guanYu (Piece.mem_all Piece.guanYu)
  rw [Bool.and_eq_true] at hguanBounds
  have hguanX : (state.pos .guanYu).x + 2 ≤ 4 := by
    simpa [Piece.shape] using (of_decide_eq_true hguanBounds.1)
  have hguanY : (state.pos .guanYu).y + 1 ≤ 5 := by
    simpa [Piece.shape] using (of_decide_eq_true hguanBounds.2)
  have hpair :=
    (List.all_eq_true.mp
      (List.all_eq_true.mp hvalid.2 Piece.caoCao (Piece.mem_all Piece.caoCao))
      Piece.guanYu (Piece.mem_all Piece.guanYu))
  rcases hguan : state.pos .guanYu with ⟨gx, gy⟩
  rw [hguan] at hguanX hguanY
  simp at hguanX hguanY
  unfold CaoBelowGuanYu
  rw [hguan, hcao]
  change gy < 3 ∧ gx < 3 ∧ 1 < gx + 2
  have hbelowY : gy < 3 := by
    have hpair' := hpair
    simp [occupiedCells, Piece.shape, hguan, hcao] at hpair'
    by_cases hgy : gy ≤ 2
    · omega
    have hgy' : gy = 3 ∨ gy = 4 := by omega
    rcases hgy' with hgy3 | hgy4
    · subst gy
      have hgx : gx ≤ 2 := by omega
      have hgxCases : gx = 0 ∨ gx = 1 ∨ gx = 2 := by omega
      rcases hgxCases with rfl | rfl | rfl
      · have h := hpair' 0 (by decide) 0 (by decide) 1 (by decide)
        simp at h
      · have h := hpair' 0 (by decide) 0 (by decide) 0 (by decide)
        simp at h
      · have h := hpair' 0 (by decide) 1 (by decide) 0 (by decide)
        simp at h
    · subst gy
      have hgx : gx ≤ 2 := by omega
      have hgxCases : gx = 0 ∨ gx = 1 ∨ gx = 2 := by omega
      rcases hgxCases with rfl | rfl | rfl
      · have h := hpair' 1 (by decide) 0 (by decide) 1 (by decide)
        simp at h
      · have h := hpair' 1 (by decide) 0 (by decide) 0 (by decide)
        simp at h
      · have h := hpair' 1 (by decide) 1 (by decide) 0 (by decide)
        simp at h
  exact ⟨hbelowY, by omega, by omega⟩

theorem solution_visits_caoBelowGuanYu (solution : Solution classic) :
    solution.path.Visits CaoBelowGuanYu := by
  apply solution.path.visits_target CaoBelowGuanYu
  exact valid_goal_caoBelowGuanYu
    (solution.target_valid classic_valid) solution.solved

theorem classic_solutionGate_caoBelowGuanYu :
    SolutionGate classic CaoBelowGuanYu := by
  intro solution
  exact solution_visits_caoBelowGuanYu solution

theorem classic116Goal_caoBelowGuanYu :
    CaoBelowGuanYu classic116Goal := by
  exact valid_goal_caoBelowGuanYu
    (classic116Solution.target_valid classic_valid)
    classic116_reaches_goal

end Huarongdao
