import Huarongdao.Transition

namespace Huarongdao

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
