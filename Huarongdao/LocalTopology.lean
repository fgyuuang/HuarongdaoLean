import Huarongdao.StateSpaceKernel

namespace Huarongdao

namespace StateSpace
namespace Task

universe u v

variable {State : Type u} {Action : Type v}

/-- Two labelled transitions commute at a state when both execution orders
    form a proof-carrying square with the same opposite vertex. -/
def ActionsCommuteAt (task : Task State Action)
    (source : State) (first second : Action) : Prop :=
  ∃ afterFirst afterSecond target,
    task.step source first afterFirst ∧
    task.step source second afterSecond ∧
    task.step afterFirst second target ∧
    task.step afterSecond first target

/-- A nondegenerate commuting square in an arbitrary state-space task. -/
def SquareAt (task : Task State Action)
    (source : State) (first second : Action) : Prop :=
  first ≠ second ∧ task.ActionsCommuteAt source first second

/-- The action link at a state: vertices are actions and edges are squares. -/
def LinkEdge (task : Task State Action)
    (source : State) (first second : Action) : Prop :=
  task.SquareAt source first second

/-- A finite family of pairwise commuting action directions at one state. -/
def PairwiseCommuteAt (task : Task State Action)
    (source : State) (actions : List Action) : Prop :=
  actions.Pairwise fun first second =>
    task.LinkEdge source first second

theorem actionsCommuteAt_symm
    {task : Task State Action} {source : State} {first second : Action} :
    task.ActionsCommuteAt source first second →
      task.ActionsCommuteAt source second first := by
  rintro ⟨afterFirst, afterSecond, target,
    firstStep, secondStep, firstThenSecond, secondThenFirst⟩
  exact
    ⟨afterSecond, afterFirst, target,
      secondStep, firstStep, secondThenFirst, firstThenSecond⟩

theorem squareAt_symm
    {task : Task State Action} {source : State} {first second : Action} :
    task.SquareAt source first second →
      task.SquareAt source second first := by
  rintro ⟨distinct, commutes⟩
  exact ⟨Ne.symm distinct, actionsCommuteAt_symm commutes⟩

theorem linkEdge_symm
    {task : Task State Action} {source : State} {first second : Action} :
    task.LinkEdge source first second →
      task.LinkEdge source second first :=
  squareAt_symm

end Task
end StateSpace

/-
The remaining definitions are the executable compatibility API on raw classic
states. The bridge theorems below identify them with the maintained legal-state
`StateSpace.Task` semantics.
-/

def tryAction (s : State) (a : Action) : Option State :=
  tryMove s a.piece a.direction

def ActionsCommuteAt (s : State) (a b : Action) : Prop :=
  ∃ sa sb target,
    tryAction s a = some sa ∧
    tryAction s b = some sb ∧
    tryAction sa b = some target ∧
    tryAction sb a = some target

def SquareAt (s : State) (a b : Action) : Prop :=
  a ≠ b ∧ ActionsCommuteAt s a b

/-- The link of a state has legal actions as vertices and commuting pairs as edges. -/
def LinkEdge (s : State) (a b : Action) : Prop :=
  SquareAt s a b

/-- A finite action family is pairwise commuting at a state. -/
def PairwiseCommuteAt (s : State) (actions : List Action) : Prop :=
  actions.Pairwise fun a b => LinkEdge s a b

/-- Executable list of all labelled actions on the classic board. -/
def Action.all : List Action :=
  Piece.all.flatMap fun piece =>
    Direction.all.map fun direction => ⟨piece, direction⟩

def checkActionsCommuteAt (s : State) (a b : Action) : Bool :=
  match tryAction s a, tryAction s b with
  | some sa, some sb =>
      match tryAction sa b, tryAction sb a with
      | some targetAB, some targetBA => targetAB == targetBA
      | _, _ => false
  | _, _ => false

theorem actionsCommuteAt_symm {s : State} {a b : Action} :
    ActionsCommuteAt s a b → ActionsCommuteAt s b a := by
  rintro ⟨sa, sb, target, ha, hb, hab, hba⟩
  exact ⟨sb, sa, target, hb, ha, hba, hab⟩

theorem squareAt_symm {s : State} {a b : Action} :
    SquareAt s a b → SquareAt s b a := by
  rintro ⟨hne, hcommute⟩
  exact ⟨Ne.symm hne, actionsCommuteAt_symm hcommute⟩

theorem linkEdge_symm {s : State} {a b : Action} :
    LinkEdge s a b → LinkEdge s b a :=
  squareAt_symm

theorem actionsCommuteAt_steps {s : State} {a b : Action}
    (h : ActionsCommuteAt s a b) :
    ∃ sa sb target, Step s sa ∧ Step s sb ∧ Step sa target ∧ Step sb target := by
  rcases h with ⟨sa, sb, target, ha, hb, hab, hba⟩
  exact ⟨sa, sb, target, ⟨a, ha⟩, ⟨b, hb⟩, ⟨b, hab⟩, ⟨a, hba⟩⟩

/-- The executable raw-state square is exactly the generic Task square once
    the source state is equipped with its legality proof. -/
theorem actionsCommuteAt_iff_concrete
    {s : State} (validSource : ValidState s) {a b : Action} :
    ActionsCommuteAt s a b ↔
      StateSpace.Task.ActionsCommuteAt
        ClassicStateSpaceKernel.concrete ⟨s, validSource⟩ a b := by
  constructor
  · rintro ⟨sa, sb, target, ha, hb, hab, hba⟩
    let validAfterA : ValidClassicState :=
      ⟨sa, tryMove_preserves_validity ha⟩
    let validAfterB : ValidClassicState :=
      ⟨sb, tryMove_preserves_validity hb⟩
    let validTarget : ValidClassicState :=
      ⟨target, tryMove_preserves_validity hab⟩
    exact
      ⟨validAfterA, validAfterB, validTarget,
        ha, hb, hab, hba⟩
  · rintro ⟨sa, sb, target, ha, hb, hab, hba⟩
    exact ⟨sa.1, sb.1, target.1, ha, hb, hab, hba⟩

theorem squareAt_iff_concrete
    {s : State} (validSource : ValidState s) {a b : Action} :
    SquareAt s a b ↔
      StateSpace.Task.SquareAt
        ClassicStateSpaceKernel.concrete ⟨s, validSource⟩ a b := by
  simp only [SquareAt, StateSpace.Task.SquareAt]
  exact and_congr Iff.rfl (actionsCommuteAt_iff_concrete validSource)

theorem linkEdge_iff_concrete
    {s : State} (validSource : ValidState s) {a b : Action} :
    LinkEdge s a b ↔
      StateSpace.Task.LinkEdge
        ClassicStateSpaceKernel.concrete ⟨s, validSource⟩ a b := by
  exact squareAt_iff_concrete validSource

theorem pairwiseCommuteAt_iff_concrete
    {s : State} (validSource : ValidState s) (actions : List Action) :
    PairwiseCommuteAt s actions ↔
      StateSpace.Task.PairwiseCommuteAt
        ClassicStateSpaceKernel.concrete ⟨s, validSource⟩ actions := by
  induction actions with
  | nil =>
      simp [PairwiseCommuteAt, StateSpace.Task.PairwiseCommuteAt]
  | cons head tail inductionHypothesis =>
      simp only [
        PairwiseCommuteAt,
        StateSpace.Task.PairwiseCommuteAt,
        List.pairwise_cons
      ]
      constructor
      · rintro ⟨headCommutes, tailCommutes⟩
        exact
          ⟨fun action member =>
              (linkEdge_iff_concrete validSource).mp
                (headCommutes action member),
            inductionHypothesis.mp tailCommutes⟩
      · rintro ⟨headCommutes, tailCommutes⟩
        exact
          ⟨fun action member =>
              (linkEdge_iff_concrete validSource).mpr
                (headCommutes action member),
            inductionHypothesis.mpr tailCommutes⟩

theorem checkActionsCommuteAt_sound {s : State} {a b : Action}
    (h : checkActionsCommuteAt s a b = true) : ActionsCommuteAt s a b := by
  cases ha : tryAction s a with
  | none => simp [checkActionsCommuteAt, ha] at h
  | some sa =>
      cases hb : tryAction s b with
      | none => simp [checkActionsCommuteAt, ha, hb] at h
      | some sb =>
          cases hab : tryAction sa b with
          | none => simp [checkActionsCommuteAt, ha, hb, hab] at h
          | some targetAB =>
              cases hba : tryAction sb a with
              | none => simp [checkActionsCommuteAt, ha, hb, hab, hba] at h
              | some targetBA =>
                  have heq : targetAB = targetBA := by
                    simpa [checkActionsCommuteAt, ha, hb, hab, hba] using h
                  subst targetBA
                  exact ⟨sa, sb, targetAB, ha, hb, hab, hba⟩

theorem checkActionsCommuteAt_complete {s : State} {a b : Action}
    (h : ActionsCommuteAt s a b) : checkActionsCommuteAt s a b = true := by
  rcases h with ⟨sa, sb, target, ha, hb, hab, hba⟩
  simp [checkActionsCommuteAt, ha, hb, hab, hba]

theorem checkActionsCommuteAt_iff {s : State} {a b : Action} :
    checkActionsCommuteAt s a b = true ↔ ActionsCommuteAt s a b :=
  ⟨checkActionsCommuteAt_sound, checkActionsCommuteAt_complete⟩

instance actionsCommuteAtDecidable (s : State) (a b : Action) :
    Decidable (ActionsCommuteAt s a b) :=
  decidable_of_iff (checkActionsCommuteAt s a b = true)
    checkActionsCommuteAt_iff

instance squareAtDecidable (s : State) (a b : Action) :
    Decidable (SquareAt s a b) := by
  unfold SquareAt
  infer_instance

instance linkEdgeDecidable (s : State) (a b : Action) :
    Decidable (LinkEdge s a b) := by
  unfold LinkEdge
  infer_instance

instance pairwiseCommuteAtDecidable (s : State) (actions : List Action) :
    Decidable (PairwiseCommuteAt s actions) := by
  unfold PairwiseCommuteAt
  infer_instance

end Huarongdao
