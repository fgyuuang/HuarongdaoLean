import Huarongdao.Symmetry
import Huarongdao.Enumeration

namespace Huarongdao

namespace Path

/-- All states visited by a proof-carrying path, including both endpoints. -/
def states : {s t : State} → Path s t → List State
  | s, _, .nil _ => [s]
  | s, _, .cons _ _ tail => s :: tail.states

/-- A path visits a region when at least one of its states satisfies the predicate. -/
def Visits (path : Path s t) (region : State → Prop) : Prop :=
  ∃ state, state ∈ path.states ∧ region state

/-- A path uses an oriented family of transitions. -/
def UsesEdge : {s t : State} → Path s t → (State → State → Prop) → Prop
  | _, _, .nil _, _ => False
  | s, _, .cons (u := u) _ _ tail, edge => edge s u ∨ tail.UsesEdge edge

/-- A path uses a transition selected by its source, action, and target. -/
def UsesTransition : {s t : State} → Path s t →
    (State → Action → State → Prop) → Prop
  | _, _, .nil _, _ => False
  | s, _, .cons (u := u) action _ tail, transition =>
      transition s action u ∨ tail.UsesTransition transition

/-- A path traverses an edge family in either orientation. -/
def UsesUndirectedEdge (path : Path s t) (edge : State → State → Prop) : Prop :=
  path.UsesEdge fun u v => edge u v ∨ edge v u

@[simp] theorem states_nil (s : State) : (Path.nil s).states = [s] := rfl

@[simp] theorem states_cons {s u t : State} (action : Action)
    (step : tryMove s action.piece action.direction = some u) (tail : Path u t) :
    (Path.cons action step tail).states = s :: tail.states := rfl

theorem visits_source (path : Path s t) (region : State → Prop) (h : region s) :
    path.Visits region := by
  refine ⟨s, ?_, h⟩
  cases path <;> simp [states]

theorem target_mem_states (path : Path s t) : t ∈ path.states := by
  induction path with
  | nil => simp [states]
  | cons _ _ tail ih => simp [states, ih]

theorem visits_target (path : Path s t) (region : State → Prop) (h : region t) :
    path.Visits region :=
  ⟨t, path.target_mem_states, h⟩

theorem visits_of_tail {s u t : State} {action : Action}
    {step : tryMove s action.piece action.direction = some u}
    {tail : Path u t} {region : State → Prop}
    (h : tail.Visits region) : (Path.cons action step tail).Visits region := by
  rcases h with ⟨state, member, inRegion⟩
  exact ⟨state, by simp [states, member], inRegion⟩

theorem visits_of_usesEdge_source (path : Path s t)
    (edge : State → State → Prop) (region : State → Prop)
    (edgeSource : ∀ {u v : State}, edge u v → region u)
    (uses : path.UsesEdge edge) : path.Visits region := by
  induction path with
  | nil => exact uses.elim
  | @cons s u t action step tail ih =>
      rcases uses with first | later
      · exact (Path.cons action step tail).visits_source region (edgeSource first)
      · exact visits_of_tail (ih later)

/--
A discrete intermediate-value principle.  If the endpoints lie on different
sides and every edge crossing sides touches `gate`, then the path visits `gate`.
-/
theorem visits_of_side_change (path : Path s t) (side : State → Bool)
    (gate : State → Prop)
    (crossing : ∀ {u v : State}, Step u v → side u ≠ side v → gate u ∨ gate v)
    (different : side s ≠ side t) : path.Visits gate := by
  induction path with
  | nil => exact (different rfl).elim
  | @cons s u t action step tail ih =>
      by_cases firstCrosses : side s = side u
      · apply visits_of_tail
        apply ih
        intro equalTail
        exact different (firstCrosses.trans equalTail)
      · rcases crossing ⟨action, step⟩ firstCrosses with sourceGate | targetGate
        · exact (Path.cons action step tail).visits_source gate sourceGate
        · apply visits_of_tail
          exact tail.visits_source gate targetGate

end Path

/-- Every path from `source` to `target` meets the selected set of vertices. -/
def VertexSeparator (cut : State → Prop) (source target : State) : Prop :=
  ∀ path : Path source target, path.Visits cut

/-- A nontrivial vertex separator excludes both endpoints from the cut. -/
def ProperVertexSeparator (cut : State → Prop) (source target : State) : Prop :=
  ¬ cut source ∧ ¬ cut target ∧ VertexSeparator cut source target

/-- Every path from `source` to `target` uses one of the selected oriented edges. -/
def EdgeSeparator (cut : State → State → Prop) (source target : State) : Prop :=
  ∀ path : Path source target, path.UsesEdge cut

/-- A vertex dominates a target when every path to the target visits that vertex. -/
def Dominates (vertex source target : State) : Prop :=
  VertexSeparator (fun state => state = vertex) source target

/-- Every completed solution from `start` must visit the gate region. -/
def SolutionGate (start : State) (gate : State → Prop) : Prop :=
  ∀ solution : Solution start, solution.path.Visits gate

/-- A region separating the start from every goal is a gate for every solution. -/
theorem solutionGate_of_separates_goals {start : State} {gate : State → Prop}
    (separates : ∀ {target : State}, goal target = true → VertexSeparator gate start target) :
    SolutionGate start gate := by
  intro solution
  exact separates solution.solved solution.path

/--
A theorem-level certificate for a separator. `side` labels two banks of the
state graph, and every transition crossing the labels must touch `gate`.
Finite checking of these fields requires a separately proved closed graph.
-/
structure GoalSeparatorCertificate (start : State) (gate : State → Prop) where
  side : State → Bool
  startSide : side start = false
  goalSide : ∀ {target : State}, goal target = true → side target = true
  crossing : ∀ {s t : State}, Step s t → side s ≠ side t → gate s ∨ gate t

namespace GoalSeparatorCertificate

theorem separates (certificate : GoalSeparatorCertificate start gate)
    {target : State} (targetGoal : goal target = true) :
    VertexSeparator gate start target := by
  intro path
  apply path.visits_of_side_change certificate.side gate certificate.crossing
  rw [certificate.startSide, certificate.goalSide targetGoal]
  decide

theorem solutionGate (certificate : GoalSeparatorCertificate start gate) :
    SolutionGate start gate :=
  solutionGate_of_separates_goals certificate.separates

end GoalSeparatorCertificate

/-- A separator certificate whose gate contains neither the start nor any goal. -/
structure ProperGoalSeparatorCertificate (start : State) (gate : State → Prop)
    extends GoalSeparatorCertificate start gate where
  startOutside : ¬ gate start
  goalsOutside : ∀ {target : State}, goal target = true → ¬ gate target

namespace ProperGoalSeparatorCertificate

theorem properSeparates (certificate : ProperGoalSeparatorCertificate start gate)
    {target : State} (targetGoal : goal target = true) :
    ProperVertexSeparator gate start target :=
  ⟨certificate.startOutside, certificate.goalsOutside targetGoal,
    certificate.toGoalSeparatorCertificate.separates targetGoal⟩

end ProperGoalSeparatorCertificate

/-- The transition relation induced on any chosen family of macrostates. -/
def MacroStep {Macro : Type} (classify : State → Macro) (source target : Macro) : Prop :=
  ∃ s t : State, classify s = source ∧ classify t = target ∧ Step s t

/--
Every concrete path induces a path through its macrostates, including
stuttering steps.  The converse need not hold: existential macro edges can
compose through different concrete representatives.
-/
inductive MacroReachable {Macro : Type} (classify : State → Macro) : Macro → Macro → Prop where
  | refl (node : Macro) : MacroReachable classify node node
  | tail {source middle target : Macro} :
      MacroStep classify source middle →
      MacroReachable classify middle target →
      MacroReachable classify source target

theorem Path.toMacroReachable {Macro : Type} (classify : State → Macro)
    (path : Path s t) : MacroReachable classify (classify s) (classify t) := by
  induction path with
  | nil => exact .refl _
  | @cons s u t action step tail ih =>
      exact .tail ⟨s, u, rfl, rfl, ⟨action, step⟩⟩ ih

/-- The exact transition used when Cao Cao descends by one cell. -/
def CaoDownStep (source target : State) : Prop :=
  tryMove source .caoCao .down = some target

/-- An action-sensitive Cao Cao downward transition. -/
def CaoDownTransition (_source : State) (action : Action) (_target : State) : Prop :=
  action.piece = .caoCao ∧ action.direction = .down

/--
An operational statement of "Guan Yu lets Cao Cao pass": every solution uses
at least one state from which Cao Cao can legally descend.  A sharper geometric
gate can replace the predicate without changing the path-level theory above.
-/
def CaoCanDescend (state : State) : Prop :=
  ∃ target, CaoDownStep state target

/-- Cells newly occupied by `mover` between two displayed states. -/
def SweepCells (source target : State) (mover : Piece) : List Pos :=
  (occupiedCells target mover).filter fun cell =>
    cell ∉ occupiedCells source mover

/-- A blocker occupies one of the cells newly swept out by the mover. -/
def BlocksSweep (source target : State) (blocker mover : Piece) : Prop :=
  ∃ cell,
    cell ∈ occupiedCells source blocker ∧
    cell ∈ SweepCells source target mover

theorem piece_beq_eq_true_iff (first second : Piece) :
    (first == second) = true ↔ first = second := by
  cases first <;> cases second <;> decide

/--
A successful move has no other piece in its newly occupied cells.  This turns
the operational collision checker into a reusable geometric statement.
-/
theorem successful_move_clears_sweep {source target : State}
    {mover blocker : Piece} {direction : Direction}
    (move : tryMove source mover direction = some target)
    (differentPiece : blocker ≠ mover) :
    ¬ BlocksSweep source target blocker mover := by
  have targetValid : ValidState target :=
    tryMove_preserves_validity move
  have targetNoOverlap : noOverlap target = true := by
    have boundsAndOverlap :
        inBounds target = true ∧ noOverlap target = true := by
      simpa [ValidState, valid] using targetValid
    exact boundsAndOverlap.2
  have blockerPosition : target.pos blocker = source.pos blocker := by
    simpa [differentPiece] using tryMove_pos (q := blocker) move
  have blockerCells :
      occupiedCells target blocker = occupiedCells source blocker := by
    unfold occupiedCells
    rw [blockerPosition]
  have allPairs := List.all_eq_true.mp targetNoOverlap blocker
    (Piece.mem_all blocker)
  have pairClear := List.all_eq_true.mp allPairs mover (Piece.mem_all mover)
  have differentBool : (blocker == mover) = false := by
    cases equalBool : (blocker == mover) with
    | false => rfl
    | true =>
        exact (differentPiece
          ((piece_beq_eq_true_iff blocker mover).mp equalBool)).elim
  simp [differentBool] at pairClear
  intro blocked
  rcases blocked with ⟨cell, inBlocker, inSweep⟩
  have inTargetBlocker : cell ∈ occupiedCells target blocker := by
    rwa [blockerCells]
  have inTargetMover : cell ∈ occupiedCells target mover :=
    (List.mem_filter.mp inSweep).1
  exact pairClear cell inTargetBlocker cell inTargetMover rfl

/--
The precise geometric gate used for "Guan Yu lets Cao Cao pass": Cao Cao can
move down, and Guan Yu occupies none of the newly swept cells.
-/
def GuanYuClearsCaoSweep (state : State) : Prop :=
  ∃ target,
    CaoDownStep state target ∧
    ¬ BlocksSweep state target .guanYu .caoCao

theorem cao_y_nonincreasing_without_down {source target : State}
    {piece : Piece} {direction : Direction}
    (move : tryMove source piece direction = some target)
    (notDown : ¬ CaoDownStep source target) :
    (target.pos .caoCao).y ≤ (source.pos .caoCao).y := by
  have position := tryMove_pos (q := .caoCao) move
  cases piece with
  | caoCao =>
      cases direction with
      | up =>
          rcases sourcePosition : source.pos .caoCao with ⟨x, y⟩
          by_cases atTop : y = 0
          · rw [position, sourcePosition]
            simp [translated, atTop]
          · rw [position, sourcePosition]
            simp [translated, atTop]
      | down => exact (notDown move).elim
      | left =>
          rcases sourcePosition : source.pos .caoCao with ⟨x, y⟩
          by_cases atLeft : x = 0
          · rw [position, sourcePosition]
            simp [translated, atLeft]
          · rw [position, sourcePosition]
            simp [translated, atLeft]
      | right =>
          rcases sourcePosition : source.pos .caoCao with ⟨x, y⟩
          rw [position, sourcePosition]
          simp [translated]
  | guanYu | zhangFei | zhaoYun | maChao | huangZhong |
      soldier1 | soldier2 | soldier3 | soldier4 =>
      have sameY : (target.pos .caoCao).y = (source.pos .caoCao).y := by
        simpa using congrArg Pos.y position
      exact Nat.le_of_eq sameY

theorem cao_y_nonincreasing_without_down_action {source target : State}
    {action : Action} (move : tryMove source action.piece action.direction = some target)
    (notDown : ¬ CaoDownTransition source action target) :
    (target.pos .caoCao).y ≤ (source.pos .caoCao).y := by
  cases action with
  | mk piece direction =>
      have position := tryMove_pos (q := .caoCao) move
      cases piece with
      | caoCao =>
          cases direction with
          | up =>
              rcases sourcePosition : source.pos .caoCao with ⟨x, y⟩
              by_cases atTop : y = 0
              · rw [position, sourcePosition]
                simp [translated, atTop]
              · rw [position, sourcePosition]
                simp [translated, atTop]
          | down => exact (notDown ⟨rfl, rfl⟩).elim
          | left =>
              rcases sourcePosition : source.pos .caoCao with ⟨x, y⟩
              by_cases atLeft : x = 0
              · rw [position, sourcePosition]
                simp [translated, atLeft]
              · rw [position, sourcePosition]
                simp [translated, atLeft]
          | right =>
              rcases sourcePosition : source.pos .caoCao with ⟨x, y⟩
              rw [position, sourcePosition]
              simp [translated]
      | guanYu | zhangFei | zhaoYun | maChao | huangZhong |
          soldier1 | soldier2 | soldier3 | soldier4 =>
          have sameY : (target.pos .caoCao).y = (source.pos .caoCao).y := by
            simpa using congrArg Pos.y position
          exact Nat.le_of_eq sameY

theorem Path.cao_y_le_of_not_uses_down (path : Path s t)
    (avoids : ¬ path.UsesEdge CaoDownStep) :
    (t.pos .caoCao).y ≤ (s.pos .caoCao).y := by
  induction path with
  | nil => exact Nat.le_refl _
  | @cons s u t action move tail ih =>
      have firstNotDown : ¬ CaoDownStep s u := by
        intro first
        exact avoids (Or.inl first)
      have tailAvoids : ¬ tail.UsesEdge CaoDownStep := by
        intro later
        exact avoids (Or.inr later)
      exact Nat.le_trans (ih tailAvoids)
        (cao_y_nonincreasing_without_down move firstNotDown)

theorem Path.cao_y_le_of_not_uses_down_action (path : Path s t)
    (avoids : ¬ path.UsesTransition CaoDownTransition) :
    (t.pos .caoCao).y ≤ (s.pos .caoCao).y := by
  induction path with
  | nil => exact Nat.le_refl _
  | @cons s u t action move tail ih =>
      have firstNotDown : ¬ CaoDownTransition s action u := by
        intro first
        exact avoids (Or.inl first)
      have tailAvoids : ¬ tail.UsesTransition CaoDownTransition := by
        intro later
        exact avoids (Or.inr later)
      exact Nat.le_trans (ih tailAvoids)
        (cao_y_nonincreasing_without_down_action move firstNotDown)

/-- Every classic solution records an actual Cao Cao/down action. -/
theorem classic_solution_uses_cao_down_action (solution : Solution classic) :
    solution.path.UsesTransition CaoDownTransition := by
  by_cases uses : solution.path.UsesTransition CaoDownTransition
  · exact uses
  · have nonincreasing := solution.path.cao_y_le_of_not_uses_down_action uses
    have targetPosition : solution.target.pos .caoCao = ⟨1, 3⟩ :=
      (goal_eq_true_iff solution.target).mp solution.solved
    rw [targetPosition] at nonincreasing
    change 3 ≤ 0 at nonincreasing
    omega

/-- Every solution of the classic layout must contain a downward Cao Cao move. -/
theorem classic_solution_uses_cao_down (solution : Solution classic) :
    solution.path.UsesEdge CaoDownStep := by
  by_cases uses : solution.path.UsesEdge CaoDownStep
  · exact uses
  · have nonincreasing := solution.path.cao_y_le_of_not_uses_down uses
    have targetPosition : solution.target.pos .caoCao = ⟨1, 3⟩ :=
      (goal_eq_true_iff solution.target).mp solution.solved
    rw [targetPosition] at nonincreasing
    change 3 ≤ 0 at nonincreasing
    omega

/-- "Guan Yu must let Cao Cao pass", in its first operational form. -/
theorem classic_solutionGate_caoCanDescend : SolutionGate classic CaoCanDescend := by
  intro solution
  apply solution.path.visits_of_usesEdge_source CaoDownStep CaoCanDescend
  · intro source target move
    exact ⟨target, move⟩
  · exact classic_solution_uses_cao_down solution

/--
Every classic solution reaches a state where Cao Cao moves downward through a
sweep region already cleared by Guan Yu.
-/
theorem classic_solutionGate_guanYuClearsCaoSweep :
    SolutionGate classic GuanYuClearsCaoSweep := by
  intro solution
  apply solution.path.visits_of_usesEdge_source
    CaoDownStep GuanYuClearsCaoSweep
  · intro source target move
    refine ⟨target, move, ?_⟩
    exact successful_move_clears_sweep move (by decide)
  · exact classic_solution_uses_cao_down solution

end Huarongdao
