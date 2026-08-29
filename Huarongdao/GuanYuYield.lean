import Huarongdao.CaoGuanGeometry
import Huarongdao.Bottleneck
import Huarongdao.ClassicSolution
import Huarongdao.Quotient
import Huarongdao.StateSpaceSymmetry

namespace Huarongdao
namespace GuanYuYieldTheory

open CaoGuanGeometry

/--
The raw board obtained by translating Cao Cao one cell down, without asking
whether the translated board is valid.  It is the geometric "next sweep"
used to measure the exit obstruction.
-/
def caoDownSweepTarget (state : State) : State :=
  (moveUnchecked state .caoCao .down).getD state

/-- Cells newly occupied by Cao Cao in the hypothetical downward move. -/
def caoDownSweepCells (state : State) : List Pos :=
  SweepCells state (caoDownSweepTarget state) .caoCao

/-- Number of Cao Cao's next downward sweep cells occupied by Guan Yu. -/
def guanYuCaoSweepBlockage (state : State) : Nat :=
  (caoDownSweepCells state).filter
    (fun cell => cell ∈ occupiedCells state .guanYu) |>.length

/-- The exit corridor is open when Cao Cao has a legal downward move. -/
def CorridorOpen (state : State) : Prop :=
  CaoCanDescend state

/-- A state at which the downward Cao Cao sweep is clear of Guan Yu. -/
def GuanYuGate (state : State) : Prop :=
  GuanYuClearsCaoSweep state

/--
"Guan Yu yields" is an action-sensitive event.  The action must be a legal
Guan Yu move and the measured obstruction of Cao Cao's next downward sweep
must strictly decrease.
-/
def GuanYuYield (source : State) (action : Action) (target : State) : Prop :=
  tryMove source action.piece action.direction = some target ∧
    action.piece = .guanYu ∧
    guanYuCaoSweepBlockage target < guanYuCaoSweepBlockage source

/-- Executable flag for the same event on a concrete legal transition. -/
def guanYuYieldFlag (source : State) (action : Action) (target : State) : Bool :=
  (tryMove source action.piece action.direction == some target) &&
    (action.piece == .guanYu) &&
    (guanYuCaoSweepBlockage target <
      guanYuCaoSweepBlockage source)

theorem GuanYuYield.is_legal
    {source target : State} {action : Action}
    (yield : GuanYuYield source action target) :
    tryMove source action.piece action.direction = some target :=
  yield.1

theorem GuanYuYield.is_guanYu
    {source target : State} {action : Action}
    (yield : GuanYuYield source action target) :
    action.piece = .guanYu :=
  yield.2.1

theorem GuanYuYield.blockage_decreases
    {source target : State} {action : Action}
    (yield : GuanYuYield source action target) :
    guanYuCaoSweepBlockage target < guanYuCaoSweepBlockage source :=
  yield.2.2

private theorem occupiedCells_relabel_fixed
    (relabeling : PieceRelabeling) (state : State)
    {piece : Piece} (fixed : relabeling.inverse piece = piece) :
    occupiedCells (relabelState relabeling state) piece =
      occupiedCells state piece := by
  rw [occupiedCells_relabel, fixed]

private theorem caoDownSweepTarget_relabel
    (relabeling : PieceRelabeling) (state : State) :
    caoDownSweepTarget (relabelState relabeling state) =
      relabelState relabeling (caoDownSweepTarget state) := by
  unfold caoDownSweepTarget
  have commute :=
    moveUnchecked_relabel relabeling state .caoCao .down
  rw [relabeling.fixedCao] at commute
  rw [commute]
  cases h : moveUnchecked state .caoCao .down with
  | none =>
      simp
  | some target =>
      simp

private theorem caoDownSweepCells_relabel
    (relabeling : PieceRelabeling) (state : State) :
    caoDownSweepCells (relabelState relabeling state) =
      caoDownSweepCells state := by
  unfold caoDownSweepCells
  rw [caoDownSweepTarget_relabel]
  simp only [SweepCells]
  rw [occupiedCells_relabel_fixed relabeling
      (caoDownSweepTarget state) relabeling.symm.fixedCao]
  rw [occupiedCells_relabel_fixed relabeling
      state relabeling.symm.fixedCao]

theorem guanYuCaoSweepBlockage_relabel
    (relabeling : PieceRelabeling) (state : State) :
    guanYuCaoSweepBlockage (relabelState relabeling state) =
      guanYuCaoSweepBlockage state := by
  unfold guanYuCaoSweepBlockage
  rw [caoDownSweepCells_relabel]
  rw [occupiedCells_relabel_fixed relabeling state
      relabeling.symm.fixedGuan]

private theorem relabel_forward_guanYu_iff
    (relabeling : PieceRelabeling) (piece : Piece) :
    relabeling.forward piece = .guanYu ↔ piece = .guanYu := by
  constructor
  · intro equal
    apply relabeling.forward_injective
    rw [equal, relabeling.fixedGuan]
  · intro equal
    rw [equal, relabeling.fixedGuan]

theorem GuanYuYield.relabel
    {source target : State} {action : Action}
    (relabeling : PieceRelabeling)
    (yield : GuanYuYield source action target) :
    GuanYuYield
      (relabelState relabeling source)
      (relabelAction relabeling action)
      (relabelState relabeling target) := by
  refine ⟨?_, ?_, ?_⟩
  · exact tryMove_relabel_some relabeling yield.1
  · exact (relabel_forward_guanYu_iff relabeling action.piece).mpr yield.2.1
  · rw [guanYuCaoSweepBlockage_relabel,
      guanYuCaoSweepBlockage_relabel]
    exact yield.2.2

private theorem relabel_inverse_eq
    (relabeling : PieceRelabeling) {state : State}
    (validState : ValidState state) :
    relabelState relabeling.symm (relabelState relabeling state) =
      state := by
  apply State.eq_of_valid_pos_eq
    (valid_relabel relabeling.symm (valid_relabel relabeling validState))
    validState
  exact relabel_inverse relabeling state

private theorem relabelAction_inverse_eq
    (relabeling : PieceRelabeling) (action : Action) :
    relabelAction relabeling.symm (relabelAction relabeling action) =
      action := by
  cases action with
  | mk piece direction =>
      simp only [relabelAction, PieceRelabeling.symm]
      rw [relabeling.leftInv]

theorem GuanYuYield.relabel_iff
    {source target : State} {action : Action}
    (relabeling : PieceRelabeling)
    (sourceValid : ValidState source)
    (targetValid : ValidState target) :
    GuanYuYield source action target ↔
      GuanYuYield
        (relabelState relabeling source)
        (relabelAction relabeling action)
        (relabelState relabeling target) := by
  constructor
  · exact GuanYuYield.relabel relabeling
  · intro relabeled
    have restored := GuanYuYield.relabel relabeling.symm relabeled
    simpa [relabel_inverse_eq relabeling sourceValid,
      relabel_inverse_eq relabeling targetValid,
      relabelAction_inverse_eq] using restored

/-- The already proved state gate is the weak "Guan Yu-related" statement. -/
theorem classic_solution_visits_guanYu_gate :
    SolutionGate classic GuanYuGate :=
  classic_solutionGate_guanYuClearsCaoSweep

/-- Every solution reaches a state at which the exit corridor is open. -/
theorem classic_solution_visits_corridor_open :
    SolutionGate classic CorridorOpen :=
  classic_solutionGate_caoCanDescend

/-!
## The logical core of the strong statement

The executable quotient search is a finite candidate certificate, but the
path-level theorem should not depend on its implementation details.  The
following certificate isolates exactly the invariant needed to lift a finite
avoidance computation to the original labelled state graph.
-/

structure YieldAvoidanceCertificate (start : State) where
  inside : State → Prop
  start_inside : inside start
  closed :
    ∀ {source action target},
      inside source →
      tryMove source action.piece action.direction = some target →
      ¬ GuanYuYield source action target →
      inside target
  goal_excluded :
    ∀ {target}, inside target → goal target = true → False

namespace YieldAvoidanceCertificate

variable {start : State}

theorem path_inside
    (certificate : YieldAvoidanceCertificate start)
    {source target : State}
    (path : Path source target)
    (source_inside : certificate.inside source)
    (avoids : ¬ path.UsesTransition GuanYuYield) :
    certificate.inside target := by
  induction path with
  | nil =>
      exact source_inside
  | @cons source middle target action step tail inductionHypothesis =>
      have first_not_yield :
          ¬ GuanYuYield source action middle := by
        intro yield
        exact avoids (Or.inl yield)
      have middle_inside :=
        certificate.closed source_inside step first_not_yield
      have tail_avoids : ¬ tail.UsesTransition GuanYuYield := by
        intro later
        exact avoids (Or.inr later)
      exact inductionHypothesis middle_inside tail_avoids

theorem no_solution_avoids_yield
    (certificate : YieldAvoidanceCertificate start)
    {target : State}
    (path : Path start target)
    (solved : goal target = true)
    (avoids : ¬ path.UsesTransition GuanYuYield) :
    False := by
  exact certificate.goal_excluded
    (certificate.path_inside path certificate.start_inside avoids) solved

theorem uses_yield
    (certificate : YieldAvoidanceCertificate start)
    {target : State}
    (path : Path start target)
    (solved : goal target = true) :
    path.UsesTransition GuanYuYield := by
  by_contra avoids
  exact certificate.no_solution_avoids_yield path solved avoids

end YieldAvoidanceCertificate

theorem classic_solution_uses_guanYu_yield_of_certificate
    (certificate : YieldAvoidanceCertificate classic)
    (solution : Solution classic) :
    solution.path.UsesTransition GuanYuYield :=
  certificate.uses_yield solution.path solution.solved

/-- A finite-node version of the avoidance certificate.  `Node` is intended
to be a canonical quotient presentation, while `represents` carries the
semantic relation back to labelled states. -/
structure FiniteYieldAvoidanceCertificate (start : State) where
  Node : Type
  represents : State → Node → Prop
  startNode : Node
  startRepresented : represents start startNode
  inside : Node → Bool
  startInside : inside startNode = true
  simulateNoYield :
    ∀ {source target : State} {node : Node} {action : Action},
      represents source node →
      tryMove source action.piece action.direction = some target →
      ¬ GuanYuYield source action target →
      ∃ next : Node,
        inside next = true ∧
        represents target next
  goalExcluded :
    ∀ {target : State} {node : Node},
      represents target node →
      inside node = true →
      goal target = true →
      False

namespace FiniteYieldAvoidanceCertificate

variable {start : State}

def toYieldAvoidanceCertificate
    (certificate : FiniteYieldAvoidanceCertificate start) :
    YieldAvoidanceCertificate start where
  inside state :=
    ∃ node, certificate.inside node = true ∧
      certificate.represents state node
  start_inside :=
    ⟨certificate.startNode, certificate.startInside,
      certificate.startRepresented⟩
  closed := by
    intro source action target sourceInside step notYield
    rcases sourceInside with ⟨node, nodeInside, represented⟩
    rcases certificate.simulateNoYield represented step notYield with
      ⟨next, nextInside, targetRepresented⟩
    exact ⟨next, nextInside, targetRepresented⟩
  goal_excluded := by
    intro target targetInside targetGoal
    rcases targetInside with ⟨node, nodeInside, represented⟩
    exact certificate.goalExcluded represented nodeInside targetGoal

theorem uses_yield
    (certificate : FiniteYieldAvoidanceCertificate start)
    {target : State}
    (path : Path start target)
    (solved : goal target = true) :
    path.UsesTransition GuanYuYield :=
  certificate.toYieldAvoidanceCertificate.uses_yield path solved

end FiniteYieldAvoidanceCertificate

theorem classic_solution_uses_guanYu_yield_of_finite_certificate
    (certificate : FiniteYieldAvoidanceCertificate classic)
    (solution : Solution classic) :
    solution.path.UsesTransition GuanYuYield :=
  certificate.uses_yield solution.path solution.solved

end GuanYuYieldTheory
end Huarongdao
