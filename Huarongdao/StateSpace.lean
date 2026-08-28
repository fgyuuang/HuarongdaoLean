import Huarongdao.Paths

namespace Huarongdao

/-
This namespace contains the graph-independent semantics of a puzzle.  The
finite arrays produced by search are presentations of these objects, rather
than the definitions of the objects themselves.
-/
namespace StateSpace

universe u v u' v' u'' v''

/-- A rooted, goal-labelled, action-labelled transition system. -/
structure Task (State : Type u) (Action : Type v) where
  initial : State
  goal : State → Prop
  step : State → Action → State → Prop

namespace Task

variable {State : Type u} {Action : Type v}

/-- The unlabelled directed edge relation obtained by forgetting the action. -/
def Moves (task : Task State Action) (source target : State) : Prop :=
  ∃ action, task.step source action target

/-- A proof-carrying walk in an action-labelled transition system. -/
inductive Walk (task : Task State Action) : State → State → Type (max u v) where
  | nil (state : State) : Walk task state state
  | cons {source middle target : State} (action : Action)
      (first : task.step source action middle)
      (tail : Walk task middle target) :
      Walk task source target

namespace Walk

variable {task : Task State Action} {source middle target : State}

/-- The action word recorded by a walk. -/
def actions : {source target : State} → task.Walk source target → List Action
  | _, _, .nil _ => []
  | _, _, .cons action _ tail => action :: actions tail

/-- The number of one-step transitions in a walk. -/
def length : {source target : State} → task.Walk source target → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ tail => length tail + 1

/-- Concatenate two proof-carrying walks. -/
def append :
    {source middle target : State} →
      task.Walk source middle →
      task.Walk middle target →
      task.Walk source target
  | _, _, _, .nil _, rightWalk => rightWalk
  | _, _, _, .cons action first tail, rightWalk =>
      .cons action first (append tail rightWalk)

@[simp] theorem actions_nil (state : State) :
    (Walk.nil (task := task) state).actions = [] :=
  rfl

@[simp] theorem actions_cons (action : Action) (first : task.step source action middle)
    (tail : task.Walk middle target) :
    (Walk.cons action first tail).actions = action :: tail.actions :=
  rfl

@[simp] theorem length_nil (state : State) :
    (Walk.nil (task := task) state).length = 0 :=
  rfl

@[simp] theorem length_cons (action : Action) (first : task.step source action middle)
    (tail : task.Walk middle target) :
    (Walk.cons action first tail).length = tail.length + 1 :=
  rfl

@[simp] theorem actions_append (leftWalk : task.Walk source middle)
    (rightWalk : task.Walk middle target) :
    (leftWalk.append rightWalk).actions =
      leftWalk.actions ++ rightWalk.actions := by
  induction leftWalk with
  | nil => rfl
  | cons action first tail ih =>
      simp [append, actions, ih]

@[simp] theorem length_append (leftWalk : task.Walk source middle)
    (rightWalk : task.Walk middle target) :
    (leftWalk.append rightWalk).length =
      leftWalk.length + rightWalk.length := by
  induction leftWalk with
  | nil => simp [append, length]
  | cons action first tail ih =>
      simp [append, length, ih, Nat.add_assoc, Nat.add_comm]

/-- All vertices visited by a walk, including both endpoints. -/
def states : {source target : State} → task.Walk source target → List State
  | source, _, .nil _ => [source]
  | source, _, .cons _ _ tail => source :: states tail

/-- A walk visits a region when one of its vertices satisfies the predicate. -/
def Visits (walk : task.Walk source target) (region : State → Prop) : Prop :=
  ∃ state, state ∈ walk.states ∧ region state

theorem visits_source (walk : task.Walk source target)
    (region : State → Prop) (source_mem : region source) :
    walk.Visits region := by
  refine ⟨source, ?_, source_mem⟩
  cases walk <;> simp [states]

theorem target_mem_states (walk : task.Walk source target) :
    target ∈ walk.states := by
  induction walk with
  | nil => simp [states]
  | cons _ _ tail ih => simp [states, ih]

theorem visits_target (walk : task.Walk source target)
    (region : State → Prop) (target_mem : region target) :
    walk.Visits region :=
  ⟨target, walk.target_mem_states, target_mem⟩

theorem visits_of_tail {action : Action} {first : task.step source action middle}
    {tail : task.Walk middle target} {region : State → Prop}
    (visits : tail.Visits region) :
    (Walk.cons action first tail).Visits region := by
  rcases visits with ⟨state, member, inRegion⟩
  exact ⟨state, by simp [states, member], inRegion⟩

/--
A discrete intermediate-value theorem for graph walks.  When the endpoints
have different Boolean side labels, and every crossing edge touches `gate`,
the walk must visit `gate`.
-/
theorem visits_of_side_change (walk : task.Walk source target)
    (side : State → Bool) (gate : State → Prop)
    (crossing :
      ∀ {u v : State} {action : Action},
        task.step u action v →
        side u ≠ side v →
        gate u ∨ gate v)
    (different : side source ≠ side target) :
    walk.Visits gate := by
  induction walk with
  | nil => exact (different rfl).elim
  | @cons source middle target action first tail ih =>
      by_cases sameFirstSide : side source = side middle
      · apply visits_of_tail
        apply ih
        intro sameTailSide
        exact different (sameFirstSide.trans sameTailSide)
      · rcases crossing first sameFirstSide with sourceGate | middleGate
        · exact (Walk.cons action first tail).visits_source gate sourceGate
        · apply visits_of_tail
          exact tail.visits_source gate middleGate

end Walk

/-- Reachability means that a proof-carrying walk exists. -/
def Reachable (task : Task State Action) (source target : State) : Prop :=
  Nonempty (task.Walk source target)

/-- A completed task solution carries its endpoint, walk, and goal proof. -/
structure Solution (task : Task State Action) where
  target : State
  walk : task.Walk task.initial target
  solved : task.goal target

namespace Solution

variable {task : Task State Action}

/-- The action word carried by a task-level solution. -/
def actions (solution : task.Solution) : List Action :=
  solution.walk.actions

/-- The number of primitive task transitions in a solution. -/
def length (solution : task.Solution) : Nat :=
  solution.walk.length

/-- A task-level solution is minimal when no solution uses fewer transitions. -/
def Minimal (solution : task.Solution) : Prop :=
  ∀ other : task.Solution, solution.length ≤ other.length

end Solution

/-- Every walk from `source` to `target` meets the selected vertex region. -/
def VertexSeparator (task : Task State Action)
    (cut : State → Prop) (source target : State) : Prop :=
  ∀ walk : task.Walk source target, walk.Visits cut

/-- Every completed solution must visit the selected gate region. -/
def SolutionGate (task : Task State Action) (gate : State → Prop) : Prop :=
  ∀ solution : task.Solution, solution.walk.Visits gate

/--
A local certificate for a global gate theorem.  The checker only needs to
verify the two endpoint labels and every one-step edge crossing the labels.
-/
structure GoalSeparatorCertificate (task : Task State Action)
    (gate : State → Prop) where
  side : State → Bool
  initialSide : side task.initial = false
  goalSide : ∀ {target}, task.goal target → side target = true
  crossing :
    ∀ {source target : State} {action : Action},
      task.step source action target →
      side source ≠ side target →
      gate source ∨ gate target

namespace GoalSeparatorCertificate

variable {task : Task State Action} {gate : State → Prop}

theorem separates (certificate : GoalSeparatorCertificate task gate)
    {target : State} (targetGoal : task.goal target) :
    task.VertexSeparator gate task.initial target := by
  intro walk
  apply walk.visits_of_side_change certificate.side gate certificate.crossing
  rw [certificate.initialSide, certificate.goalSide targetGoal]
  decide

theorem solutionGate (certificate : GoalSeparatorCertificate task gate) :
    task.SolutionGate gate := by
  intro solution
  exact certificate.separates solution.solved solution.walk

end GoalSeparatorCertificate

/-- The mathematically exact vertex type of the rooted reachable state space. -/
abbrev Vertex (task : Task State Action) :=
  { state : State // task.Reachable task.initial state }

namespace Vertex

variable {task : Task State Action}

/-- The initial state, carrying its reflexive reachability proof. -/
def initial : task.Vertex :=
  ⟨task.initial, ⟨Walk.nil task.initial⟩⟩

/-- The goal predicate restricted to the reachable state space. -/
def Goal (state : task.Vertex) : Prop :=
  task.goal state.1

/-- The action-labelled edge relation restricted to reachable vertices. -/
def Step (source : task.Vertex) (action : Action) (target : task.Vertex) : Prop :=
  task.step source.1 action target.1

/-- Forget the action label on an edge between reachable vertices. -/
def Adj (source target : task.Vertex) : Prop :=
  task.Moves source.1 target.1

end Vertex

/-- A simulation preserving the root, goals, actions, and transitions. -/
structure Hom
    (sourceTask : Task State Action)
    (targetTask : Task (State' : Type u') (Action' : Type v')) where
  mapState : State → State'
  mapAction : Action → Action'
  map_initial : mapState sourceTask.initial = targetTask.initial
  map_goal : ∀ {state}, sourceTask.goal state → targetTask.goal (mapState state)
  map_step : ∀ {source action target},
    sourceTask.step source action target →
      targetTask.step (mapState source) (mapAction action) (mapState target)

namespace Hom

variable {State' : Type u'} {Action' : Type v'}
variable {sourceTask : Task State Action} {targetTask : Task State' Action'}

/-- Identity simulation of a state-space task. -/
def id (task : Task State Action) : Hom task task where
  mapState := fun state => state
  mapAction := fun action => action
  map_initial := rfl
  map_goal := fun goal => goal
  map_step := fun step => step

/-- Compose simulations between state-space tasks. -/
def comp
    {State'' : Type u''} {Action'' : Type v''}
    {finalTask : Task State'' Action''}
    (right : Hom targetTask finalTask)
    (left : Hom sourceTask targetTask) :
    Hom sourceTask finalTask where
  mapState := right.mapState ∘ left.mapState
  mapAction := right.mapAction ∘ left.mapAction
  map_initial := by
    change right.mapState (left.mapState sourceTask.initial) =
      finalTask.initial
    rw [left.map_initial, right.map_initial]
  map_goal := fun goal => right.map_goal (left.map_goal goal)
  map_step := fun step => right.map_step (left.map_step step)

/-- A simulation maps every concrete walk to a walk in the target system. -/
def mapWalk (hom : Hom sourceTask targetTask) :
    sourceTask.Walk source target →
      targetTask.Walk (hom.mapState source) (hom.mapState target)
  | .nil _ => .nil _
  | .cons action first tail =>
      .cons (hom.mapAction action) (hom.map_step first) (hom.mapWalk tail)

@[simp] theorem mapWalk_length (hom : Hom sourceTask targetTask)
    (walk : sourceTask.Walk source target) :
    (hom.mapWalk walk).length = walk.length := by
  induction walk with
  | nil => rfl
  | cons action first tail ih =>
      simp [mapWalk, Walk.length, ih]

theorem map_reachable (hom : Hom sourceTask targetTask)
    (reachable : sourceTask.Reachable source target) :
    targetTask.Reachable (hom.mapState source) (hom.mapState target) := by
  rcases reachable with ⟨walk⟩
  exact ⟨hom.mapWalk walk⟩

theorem goal_preserved (hom : Hom sourceTask targetTask)
    {state : State} (goal : sourceTask.goal state) :
    targetTask.goal (hom.mapState state) :=
  hom.map_goal goal

end Hom

end Task

/--
An observation identifies states while requiring the goal predicate to be
constant on every equivalence class.  This is the minimum data needed for a
well-defined quotient goal predicate.
-/
structure Observation {State : Type u} {Action : Type v}
    (task : Task State Action) : Type (max u v) where
  setoid : Setoid State
  goal_iff : ∀ {source target}, setoid.r source target →
    (task.goal source ↔ task.goal target)

namespace Observation

variable {State : Type u} {Action : Type v} {task : Task State Action}

/-- A node in the state quotient induced by an observation. -/
abbrev Node (observation : Observation task) :=
  Quotient observation.setoid

/-- Project a concrete state to its observational equivalence class. -/
def classOf (observation : Observation task) (state : State) : observation.Node :=
  Quotient.mk observation.setoid state

/-- The goal predicate descended to observational equivalence classes. -/
def Goal (observation : Observation task) (node : observation.Node) : Prop :=
  Quotient.liftOn node task.goal fun _source _target equivalent =>
    propext (observation.goal_iff equivalent)

@[simp] theorem goal_classOf (observation : Observation task) (state : State) :
    observation.Goal (observation.classOf state) ↔ task.goal state :=
  Iff.rfl

/--
The relational image of the concrete transition relation.  This definition is
always a sound abstraction, but composable quotient paths require the stronger
representative-wise condition in `BisimulationQuotient`.
-/
def Step (observation : Observation task)
    (source target : observation.Node) : Prop :=
  ∃ concreteSource : State, ∃ action : Action, ∃ concreteTarget : State,
    observation.classOf concreteSource = source ∧
    observation.classOf concreteTarget = target ∧
    task.step concreteSource action concreteTarget

theorem step_of_step (observation : Observation task)
    {source target : State} {action : Action}
    (step : task.step source action target) :
    observation.Step
      (observation.classOf source)
      (observation.classOf target) :=
  ⟨source, action, target, rfl, rfl, step⟩

/--
Every observation induces another state-space object.  Its states are
equivalence classes, its actions are unlabelled quotient edges, and its root
and goal predicate descend from the concrete task.
-/
def quotientTask (observation : Observation task) :
    Task observation.Node Unit where
  initial := observation.classOf task.initial
  goal := observation.Goal
  step := fun source _ target => observation.Step source target

/-- The canonical projection from a task to any of its observational quotients. -/
def projectionHom (observation : Observation task) :
    Task.Hom task observation.quotientTask where
  mapState := observation.classOf
  mapAction := fun _ => ()
  map_initial := rfl
  map_goal := by
    intro state goal
    exact (observation.goal_classOf state).mpr goal
  map_step := by
    intro source action target step
    exact observation.step_of_step step

/-- A proof-carrying walk in the relational-image quotient graph. -/
inductive QuotientWalk (observation : Observation task) :
    observation.Node → observation.Node → Type (max u v) where
  | nil (node : observation.Node) : QuotientWalk observation node node
  | cons {source middle target : observation.Node}
      (first : observation.Step source middle)
      (tail : QuotientWalk observation middle target) :
      QuotientWalk observation source target

namespace QuotientWalk

variable {observation : Observation task}

/-- The number of quotient edges traversed by a quotient walk. -/
def length :
    {source target : observation.Node} →
      observation.QuotientWalk source target →
      Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => length tail + 1

/-- Every concrete walk projects to the quotient graph. -/
def ofWalk :
    task.Walk source target →
      observation.QuotientWalk
        (observation.classOf source)
        (observation.classOf target)
  | .nil _ => .nil _
  | .cons _action first tail =>
      .cons (observation.step_of_step first) (ofWalk tail)

@[simp] theorem length_ofWalk (walk : task.Walk source target) :
    (ofWalk (observation := observation) walk).length = walk.length := by
  induction walk with
  | nil => rfl
  | cons action first tail ih =>
      simp [ofWalk, length, Task.Walk.length, ih]

/-- Reinterpret a quotient walk as a walk in the induced quotient task. -/
def toTaskWalk :
    observation.QuotientWalk source target →
      observation.quotientTask.Walk source target
  | .nil node => .nil node
  | .cons first tail => .cons () first (toTaskWalk tail)

/-- Reinterpret a quotient-task walk using the compatibility quotient-walk type. -/
def ofTaskWalk :
    observation.quotientTask.Walk source target →
      observation.QuotientWalk source target
  | .nil node => .nil node
  | .cons _ first tail => .cons first (ofTaskWalk tail)

@[simp] theorem length_toTaskWalk
    (walk : observation.QuotientWalk source target) :
    walk.toTaskWalk.length = walk.length := by
  induction walk with
  | nil => rfl
  | cons first tail ih =>
      simp [toTaskWalk, length, Task.Walk.length, ih]

@[simp] theorem length_ofTaskWalk
    (walk : observation.quotientTask.Walk source target) :
    (ofTaskWalk walk).length = walk.length := by
  induction walk with
  | nil => rfl
  | cons action first tail ih =>
      simp [ofTaskWalk, length, Task.Walk.length, ih]

@[simp] theorem ofTaskWalk_toTaskWalk
    (walk : observation.QuotientWalk source target) :
    ofTaskWalk walk.toTaskWalk = walk := by
  induction walk with
  | nil => rfl
  | cons first tail ih =>
      simp [toTaskWalk, ofTaskWalk, ih]

@[simp] theorem toTaskWalk_ofTaskWalk
    (walk : observation.quotientTask.Walk source target) :
    (ofTaskWalk walk).toTaskWalk = walk := by
  induction walk with
  | nil => rfl
  | cons action first tail ih =>
      cases action
      simp [toTaskWalk, ofTaskWalk, ih]

/-- Reachability in the relational-image quotient graph. -/
def Reachable (source target : observation.Node) : Prop :=
  Nonempty (observation.QuotientWalk source target)

end QuotientWalk

end Observation

/--
A quotient is a bisimulation quotient when every step made by one
representative can be matched from every equivalent representative.  Actions
may be renamed, but the resulting targets must remain equivalent.
-/
structure BisimulationQuotient {State : Type u} {Action : Type v}
    (task : Task State Action) : Type (max u v) extends Observation task where
  step_lift :
    ∀ {source source' : State} {action : Action} {target : State},
      toObservation.setoid.r source source' →
      task.step source action target →
      ∃ action' target',
        task.step source' action' target' ∧
        toObservation.setoid.r target target'

namespace BisimulationQuotient

variable {State : Type u} {Action : Type v} {task : Task State Action}

/--
Lift one quotient edge from an arbitrary representative of its source class.
This theorem rules out the incompatible-representative defect of existential
quotient edges.
-/
theorem liftStepFrom (quotient : BisimulationQuotient task)
    {sourceClass targetClass : quotient.toObservation.Node}
    (edge : quotient.toObservation.Step sourceClass targetClass)
    (source : State)
    (source_eq : quotient.toObservation.classOf source = sourceClass) :
    ∃ action target,
      task.step source action target ∧
      quotient.toObservation.classOf target = targetClass := by
  rcases edge with
    ⟨edgeSource, edgeAction, edgeTarget, edgeSource_eq, edgeTarget_eq, edgeStep⟩
  have sourceEquivalent :
      quotient.toObservation.setoid.r edgeSource source :=
    Quotient.exact (edgeSource_eq.trans source_eq.symm)
  rcases quotient.step_lift sourceEquivalent edgeStep with
    ⟨liftedAction, liftedTarget, liftedStep, targetEquivalent⟩
  refine ⟨liftedAction, liftedTarget, liftedStep, ?_⟩
  exact (Quotient.sound targetEquivalent).symm.trans edgeTarget_eq

/-- Lift a whole quotient walk from any representative of its source class. -/
theorem liftWalkFrom (quotient : BisimulationQuotient task)
    {sourceClass targetClass : quotient.toObservation.Node}
    (walk : quotient.toObservation.QuotientWalk sourceClass targetClass)
    (source : State)
    (source_eq : quotient.toObservation.classOf source = sourceClass) :
    ∃ target,
      task.Reachable source target ∧
      quotient.toObservation.classOf target = targetClass := by
  induction walk generalizing source with
  | nil =>
      exact ⟨source, ⟨.nil source⟩, source_eq⟩
  | @cons sourceClass middleClass targetClass first tail ih =>
      rcases quotient.liftStepFrom first source source_eq with
        ⟨action, middle, firstStep, middle_eq⟩
      rcases ih middle middle_eq with ⟨target, ⟨liftedTail⟩, target_eq⟩
      exact ⟨target, ⟨.cons action firstStep liftedTail⟩, target_eq⟩

/--
The lifted concrete walk contains exactly one concrete transition for each
quotient edge.  This is the length-preserving form needed for shortest-path
arguments on an exact quotient.
-/
theorem liftWalkWithLength (quotient : BisimulationQuotient task)
    {sourceClass targetClass : quotient.toObservation.Node}
    (walk : quotient.toObservation.QuotientWalk sourceClass targetClass)
    (source : State)
    (source_eq : quotient.toObservation.classOf source = sourceClass) :
    ∃ target, ∃ concreteWalk : task.Walk source target,
      concreteWalk.length = walk.length ∧
      quotient.toObservation.classOf target = targetClass := by
  induction walk generalizing source with
  | nil =>
      exact ⟨source, .nil source, rfl, source_eq⟩
  | @cons sourceClass middleClass targetClass first tail ih =>
      rcases quotient.liftStepFrom first source source_eq with
        ⟨action, middle, firstStep, middle_eq⟩
      rcases ih middle middle_eq with
        ⟨target, concreteTail, tailLength, target_eq⟩
      refine ⟨target, .cons action firstStep concreteTail, ?_, target_eq⟩
      simp [Task.Walk.length, Observation.QuotientWalk.length, tailLength]

/--
Task-level form of `liftWalkWithLength`.  This is the preferred interface for
composing several state-space layers because every layer remains a `Task`.
-/
theorem liftTaskWalkWithLength (quotient : BisimulationQuotient task)
    {sourceClass targetClass : quotient.toObservation.Node}
    (walk :
      quotient.toObservation.quotientTask.Walk sourceClass targetClass)
    (source : State)
    (source_eq : quotient.toObservation.classOf source = sourceClass) :
    ∃ target, ∃ concreteWalk : task.Walk source target,
      concreteWalk.length = walk.length ∧
      quotient.toObservation.classOf target = targetClass := by
  rcases quotient.liftWalkWithLength
      (Observation.QuotientWalk.ofTaskWalk walk) source source_eq with
    ⟨target, concreteWalk, length_eq, target_eq⟩
  exact ⟨target, concreteWalk,
    length_eq.trans
      (Observation.QuotientWalk.length_ofTaskWalk walk),
    target_eq⟩

/--
For a bisimulation quotient, abstract reachability from a concrete class is
equivalent to concrete reachability from every chosen representative.
-/
theorem quotientReachable_iff (quotient : BisimulationQuotient task)
    (source : State) (targetClass : quotient.toObservation.Node) :
    Observation.QuotientWalk.Reachable
        (observation := quotient.toObservation)
        (quotient.toObservation.classOf source)
        targetClass ↔
      ∃ target,
        task.Reachable source target ∧
        quotient.toObservation.classOf target = targetClass := by
  constructor
  · rintro ⟨walk⟩
    rcases quotient.liftWalkFrom walk source rfl with
      ⟨target, reachable, target_eq⟩
    exact ⟨target, reachable, target_eq⟩
  · rintro ⟨target, ⟨walk⟩, target_eq⟩
    rw [← target_eq]
    exact ⟨Observation.QuotientWalk.ofWalk walk⟩

end BisimulationQuotient

/-- The classic puzzle as a rooted, goal-labelled, action-labelled system. -/
def classicTask : Task State Action where
  initial := classic
  goal := fun state => goal state = true
  step := fun source action target =>
    tryMove source action.piece action.direction = some target

/-- The original puzzle path maps definitionally to the generic task walk. -/
def classicWalkOfPath :
    {source target : State} → Path source target → classicTask.Walk source target
  | _, _, .nil state => .nil state
  | _, _, .cons action first tail =>
      .cons action first (classicWalkOfPath tail)

/-- The generic classic-task walk maps back to the original puzzle path. -/
def pathOfClassicWalk :
    {source target : State} → classicTask.Walk source target → Path source target
  | _, _, .nil state => .nil state
  | _, _, .cons action first tail =>
      .cons action first (pathOfClassicWalk tail)

@[simp] theorem pathOfClassicWalk_classicWalkOfPath (path : Path source target) :
    pathOfClassicWalk (classicWalkOfPath path) = path := by
  induction path with
  | nil => rfl
  | cons action first tail ih =>
      simp [classicWalkOfPath, pathOfClassicWalk, ih]

@[simp] theorem classicWalkOfPath_pathOfClassicWalk
    (walk : classicTask.Walk source target) :
    classicWalkOfPath (pathOfClassicWalk walk) = walk := by
  induction walk with
  | nil => rfl
  | cons action first tail ih =>
      simp [classicWalkOfPath, pathOfClassicWalk, ih]

@[simp] theorem classicWalkOfPath_actions (path : Path source target) :
    (classicWalkOfPath path).actions = path.actions := by
  induction path with
  | nil => rfl
  | cons action first tail ih =>
      simp [classicWalkOfPath, Task.Walk.actions, Path.actions, ih]

@[simp] theorem classicWalkOfPath_length (path : Path source target) :
    (classicWalkOfPath path).length = path.length := by
  induction path with
  | nil => rfl
  | cons action first tail ih =>
      simp [classicWalkOfPath, Task.Walk.length, Path.length, ih]

@[simp] theorem pathOfClassicWalk_actions
    (walk : classicTask.Walk source target) :
    (pathOfClassicWalk walk).actions = walk.actions := by
  rw [← classicWalkOfPath_actions (pathOfClassicWalk walk)]
  simp

@[simp] theorem pathOfClassicWalk_length
    (walk : classicTask.Walk source target) :
    (pathOfClassicWalk walk).length = walk.length := by
  rw [← classicWalkOfPath_length (pathOfClassicWalk walk)]
  simp

/-- Legacy classic reachability embeds into the canonical task reachability. -/
theorem classicTask_reachable_of_reachable
    (reachable : Huarongdao.Reachable source target) :
    classicTask.Reachable source target := by
  induction reachable with
  | refl state => exact ⟨.nil state⟩
  | tail step _ ih =>
      rcases step with ⟨action, executed⟩
      rcases ih with ⟨tail⟩
      exact ⟨.cons action executed tail⟩

/-- Task reachability maps back to the compatibility reachability predicate. -/
theorem reachable_of_classicTask_reachable
    (reachable : classicTask.Reachable source target) :
    Huarongdao.Reachable source target := by
  rcases reachable with ⟨walk⟩
  exact (pathOfClassicWalk walk).toReachable

theorem classicTask_reachable_iff :
    classicTask.Reachable source target ↔
      Huarongdao.Reachable source target :=
  ⟨reachable_of_classicTask_reachable, classicTask_reachable_of_reachable⟩

/-- Convert the compatibility solution object to the canonical task solution. -/
def classicTaskSolutionOfSolution
    (solution : Huarongdao.Solution classic) :
    classicTask.Solution where
  target := solution.target
  walk := classicWalkOfPath solution.path
  solved := solution.solved

/-- Recover the compatibility solution object from the canonical task solution. -/
def solutionOfClassicTaskSolution
    (solution : classicTask.Solution) :
    Huarongdao.Solution classic where
  target := solution.target
  path := pathOfClassicWalk solution.walk
  solved := solution.solved

@[simp] theorem solutionOfClassicTaskSolution_classicTaskSolutionOfSolution
    (solution : Huarongdao.Solution classic) :
    solutionOfClassicTaskSolution (classicTaskSolutionOfSolution solution) =
      solution := by
  cases solution with
  | mk target path solved =>
      rw [Huarongdao.Solution.mk.injEq]
      exact ⟨rfl, heq_of_eq (pathOfClassicWalk_classicWalkOfPath path)⟩

@[simp] theorem classicTaskSolutionOfSolution_solutionOfClassicTaskSolution
    (solution : classicTask.Solution) :
    classicTaskSolutionOfSolution (solutionOfClassicTaskSolution solution) =
      solution := by
  cases solution with
  | mk target walk solved =>
      rw [Task.Solution.mk.injEq]
      exact ⟨rfl, heq_of_eq (classicWalkOfPath_pathOfClassicWalk walk)⟩

@[simp] theorem classicTaskSolutionOfSolution_actions
    (solution : Huarongdao.Solution classic) :
    (classicTaskSolutionOfSolution solution).actions = solution.actions :=
  classicWalkOfPath_actions solution.path

@[simp] theorem classicTaskSolutionOfSolution_length
    (solution : Huarongdao.Solution classic) :
    (classicTaskSolutionOfSolution solution).length = solution.length :=
  classicWalkOfPath_length solution.path

@[simp] theorem solutionOfClassicTaskSolution_actions
    (solution : classicTask.Solution) :
    (solutionOfClassicTaskSolution solution).actions = solution.actions :=
  pathOfClassicWalk_actions solution.walk

@[simp] theorem solutionOfClassicTaskSolution_length
    (solution : classicTask.Solution) :
    (solutionOfClassicTaskSolution solution).length = solution.length :=
  pathOfClassicWalk_length solution.walk

theorem classicTaskSolution_minimal_iff
    (solution : Huarongdao.Solution classic) :
    (classicTaskSolutionOfSolution solution).Minimal ↔ solution.Minimal := by
  constructor
  · intro minimal other
    have bound := minimal (classicTaskSolutionOfSolution other)
    simpa using bound
  · intro minimal other
    have bound := minimal (solutionOfClassicTaskSolution other)
    simpa using bound

end StateSpace

end Huarongdao
