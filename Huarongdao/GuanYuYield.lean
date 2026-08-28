import Huarongdao.CaoGuanGeometry
import Huarongdao.Bottleneck
import Huarongdao.ClassicSolution

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

/-- The already proved state gate is the weak "Guan Yu-related" statement. -/
theorem classic_solution_visits_guanYu_gate :
    SolutionGate classic GuanYuGate :=
  classic_solutionGate_guanYuClearsCaoSweep

/-- Every solution reaches a state at which the exit corridor is open. -/
theorem classic_solution_visits_corridor_open :
    SolutionGate classic CorridorOpen :=
  classic_solutionGate_caoCanDescend

end GuanYuYieldTheory
end Huarongdao
