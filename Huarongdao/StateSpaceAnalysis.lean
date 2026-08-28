import Huarongdao.SymmetryShortestPath
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.List.Nodup

namespace Huarongdao
namespace StateSpace

universe u v u' v'

namespace Task

variable {State : Type u} {Action : Type v}

/-- `distance` is the least length of a walk between two fixed states. -/
def ShortestWalkLength (task : Task State Action)
    (source target : State) (distance : Nat) : Prop :=
  task.HasWalkLength source target distance ∧
    ∀ candidate, task.HasWalkLength source target candidate →
      distance ≤ candidate

theorem shortestWalkLength_unique
    {task : Task State Action} {source target : State}
    {left right : Nat}
    (leftShortest : task.ShortestWalkLength source target left)
    (rightShortest : task.ShortestWalkLength source target right) :
    left = right :=
  Nat.le_antisymm
    (leftShortest.2 right rightShortest.1)
    (rightShortest.2 left leftShortest.1)

namespace Walk

variable {task : Task State Action} {source target : State}

/-- A walk uses one of a selected family of labelled transitions. -/
def UsesTransition :
    {source target : State} → task.Walk source target →
      (State → Action → State → Prop) → Prop
  | _, _, .nil _, _ => False
  | source, _, .cons (middle := middle) action _ tail, selected =>
      selected source action middle ∨ tail.UsesTransition selected

@[simp] theorem states_mapWalk
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    (hom : Task.Hom task targetTask)
    (walk : task.Walk source target) :
    (hom.mapWalk walk).states = walk.states.map hom.mapState := by
  induction walk with
  | nil =>
      rfl
  | cons action first tail inductionHypothesis =>
      simp [Task.Hom.mapWalk, states, inductionHypothesis]

theorem visits_mapWalk_iff
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    (hom : Task.Hom task targetTask)
    (walk : task.Walk source target)
    (region : State' → Prop) :
    (hom.mapWalk walk).Visits region ↔
      walk.Visits (fun state => region (hom.mapState state)) := by
  simp [Visits, states_mapWalk]

theorem usesTransition_mapWalk_iff
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    (hom : Task.Hom task targetTask)
    (walk : task.Walk source target)
    (selected : State' → Action' → State' → Prop) :
    (hom.mapWalk walk).UsesTransition selected ↔
      walk.UsesTransition fun source action target =>
        selected
          (hom.mapState source)
          (hom.mapAction action)
          (hom.mapState target) := by
  induction walk with
  | nil =>
      rfl
  | cons action first tail inductionHypothesis =>
      simp [Task.Hom.mapWalk, UsesTransition, inductionHypothesis]

end Walk

/-- Every walk from `source` to `target` uses a selected transition family. -/
def EdgeSeparator (task : Task State Action)
    (selected : State → Action → State → Prop)
    (source target : State) : Prop :=
  ∀ walk : task.Walk source target, walk.UsesTransition selected

namespace Hom

variable {State' : Type u'} {Action' : Type v'}
variable {sourceTask : Task State Action}
variable {targetTask : Task State' Action'}

/-- A simulation maps the entire rooted reachable state space. -/
def mapVertex (hom : Hom sourceTask targetTask) :
    sourceTask.Vertex → targetTask.Vertex :=
  fun vertex =>
    ⟨hom.mapState vertex.1, by
      simpa [hom.map_initial] using
        hom.map_reachable vertex.2⟩

@[simp] theorem mapVertex_state
    (hom : Hom sourceTask targetTask)
    (vertex : sourceTask.Vertex) :
    (hom.mapVertex vertex).1 = hom.mapState vertex.1 :=
  rfl

@[simp] theorem mapVertex_initial
    (hom : Hom sourceTask targetTask) :
    hom.mapVertex (Task.Vertex.initial (task := sourceTask)) =
      Task.Vertex.initial (task := targetTask) := by
  apply Subtype.ext
  exact hom.map_initial

/-- A quotient-side vertex cut pulls back to a cut in every finer layer. -/
theorem vertexSeparator_preimage
    (hom : Hom sourceTask targetTask)
    {cut : State' → Prop} {source target : State}
    (separator :
      targetTask.VertexSeparator cut
        (hom.mapState source) (hom.mapState target)) :
    sourceTask.VertexSeparator
      (fun state => cut (hom.mapState state)) source target := by
  intro walk
  exact
    (walk.visits_mapWalk_iff hom cut).mp
      (separator (hom.mapWalk walk))

/--
A quotient-side bridge or edge cut pulls back to the full family of concrete
transitions projected onto it. It need not be a single concrete bridge.
-/
theorem edgeSeparator_preimage
    (hom : Hom sourceTask targetTask)
    {selected : State' → Action' → State' → Prop}
    {source target : State}
    (separator :
      targetTask.EdgeSeparator selected
        (hom.mapState source) (hom.mapState target)) :
    sourceTask.EdgeSeparator
      (fun source action target =>
        selected
          (hom.mapState source)
          (hom.mapAction action)
          (hom.mapState target))
      source target := by
  intro walk
  exact
    (walk.usesTransition_mapWalk_iff hom selected).mp
      (separator (hom.mapWalk walk))

end Hom

/--
A root distance labelling with the local properties produced by a complete
BFS. It is independent of arrays, hash tables, and the concrete state type.
-/
structure RootedDistanceCertificate
    (task : Task State Action) (distance : State → Nat) : Prop where
  root_zero : distance task.initial = 0
  step :
    ∀ {source action target},
      task.step source action target →
        distance target ≤ distance source + 1
  predecessor :
    ∀ target, target ≠ task.initial →
      ∃ source action,
        task.step source action target ∧
        distance target = distance source + 1

namespace RootedDistanceCertificate

variable {task : Task State Action} {distance : State → Nat}

theorem distance_le_walk_length
    (certificate : RootedDistanceCertificate task distance)
    (walk : task.Walk source target) :
    distance target ≤ distance source + walk.length := by
  induction walk with
  | nil =>
      simp
  | cons action first tail inductionHypothesis =>
      have firstBound := certificate.step first
      simp only [Walk.length_cons]
      omega

/-- Certified predecessor links reconstruct a root walk of exactly the rank. -/
theorem exists_root_walk
    (certificate : RootedDistanceCertificate task distance)
    (target : State) :
    ∃ walk : task.Walk task.initial target,
      walk.length = distance target := by
  have build :
      ∀ rank target, distance target = rank →
        ∃ walk : task.Walk task.initial target,
          walk.length = distance target := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank inductionHypothesis =>
        intro target rankEq
        by_cases atRoot : target = task.initial
        · subst target
          exact ⟨.nil _, by simp [certificate.root_zero]⟩
        · rcases certificate.predecessor target atRoot with
            ⟨previous, action, previousStep, predecessorRank⟩
          have previousLt : distance previous < rank := by
            omega
          rcases inductionHypothesis
              (distance previous) previousLt previous rfl with
            ⟨prefixWalk, prefixLength⟩
          let last : task.Walk previous target :=
            .cons action previousStep (.nil target)
          refine ⟨prefixWalk.append last, ?_⟩
          simp [last, prefixLength, predecessorRank]
  exact build (distance target) target rfl

/-- A complete BFS rank is exactly the shortest root-to-vertex distance. -/
theorem shortestWalkLength
    (certificate : RootedDistanceCertificate task distance)
    (target : State) :
    task.ShortestWalkLength task.initial target (distance target) := by
  constructor
  · rcases certificate.exists_root_walk target with
      ⟨walk, walkLength⟩
    exact ⟨walk, walkLength⟩
  · rintro candidate ⟨walk, walkLength⟩
    have lower := certificate.distance_le_walk_length walk
    rw [certificate.root_zero, zero_add, walkLength] at lower
    exact lower

end RootedDistanceCertificate

end Task

/--
A finite, complete presentation of the whole rooted reachable state space.
The array is not merely a collection of discovered states: `reachable` and
`closed` prove that it is exactly the task's reachable component.
-/
structure FiniteStateSpace
    {State : Type u} {Action : Type v}
    (task : Task State Action) where
  states : Array State
  root : Fin states.size
  root_eq_initial : states[root] = task.initial
  nodup : states.toList.Nodup
  reachable :
    ∀ index : Fin states.size,
      task.Reachable task.initial states[index]
  closed :
    ∀ (source : Fin states.size) {action target},
      task.step states[source] action target →
        ∃ targetIndex : Fin states.size,
          states[targetIndex] = target

namespace FiniteStateSpace

variable {State : Type u} {Action : Type v}
variable {task : Task State Action}

/-- The task transported to finite array indices. -/
def indexTask (space : FiniteStateSpace task) :
    Task (Fin space.states.size) Action where
  initial := space.root
  goal := fun index => task.goal space.states[index]
  step := fun source action target =>
    task.step space.states[source] action space.states[target]

/-- A typed edge whose endpoints are indices in one complete state space. -/
structure Edge (space : FiniteStateSpace task) where
  source : Fin space.states.size
  action : Action
  target : Fin space.states.size

namespace Edge

def Valid (edge : Edge space) : Prop :=
  space.indexTask.step edge.source edge.action edge.target

end Edge

/--
An exact edge-array presentation. `sound` rejects spurious exported edges;
`complete` ensures every semantic labelled transition occurs in the array.
-/
structure EdgeTable (space : FiniteStateSpace task) where
  edges : Array (Edge space)
  sound : ∀ edge, edge ∈ edges.toList → edge.Valid
  complete :
    ∀ {source action target},
      space.indexTask.step source action target →
        ∃ edge ∈ edges.toList,
          edge.source = source ∧
          edge.action = action ∧
          edge.target = target

/-- Interpret an array index as a vertex of the semantic reachable space. -/
def toVertex (space : FiniteStateSpace task)
    (index : Fin space.states.size) : task.Vertex :=
  ⟨space.states[index], space.reachable index⟩

theorem toVertex_injective (space : FiniteStateSpace task) :
    Function.Injective space.toVertex := by
  intro left right equal
  apply Fin.ext
  apply (space.nodup.getElem_inj_iff).mp
  exact congrArg Subtype.val equal

/--
Every semantic walk can be replayed in the finite index task, preserving its
actions, endpoint, and length. This is the proof-level contract of enumeration.
-/
theorem liftWalk
    (space : FiniteStateSpace task)
    {source target : State}
    (sourceIndex : Fin space.states.size)
    (sourceEq : space.states[sourceIndex] = source)
    (walk : task.Walk source target) :
    ∃ targetIndex : Fin space.states.size,
      ∃ indexWalk : space.indexTask.Walk sourceIndex targetIndex,
        space.states[targetIndex] = target ∧
        indexWalk.length = walk.length := by
  induction walk generalizing sourceIndex with
  | nil =>
      exact ⟨sourceIndex, .nil sourceIndex, sourceEq, rfl⟩
  | @cons source middle target action first tail inductionHypothesis =>
      have semanticStep :
          task.step space.states[sourceIndex] action middle := by
        simpa [sourceEq] using first
      rcases space.closed sourceIndex semanticStep with
        ⟨middleIndex, middleEq⟩
      have indexedStep :
          space.indexTask.step sourceIndex action middleIndex := by
        change task.step space.states[sourceIndex] action
          space.states[middleIndex]
        rw [middleEq]
        exact semanticStep
      rcases inductionHypothesis middleIndex middleEq with
        ⟨targetIndex, tailWalk, targetEq, tailLength⟩
      refine
        ⟨targetIndex, .cons action ?_ tailWalk, targetEq, ?_⟩
      · exact indexedStep
      · simp [tailLength]

theorem represents_walk
    (space : FiniteStateSpace task)
    {source target : State}
    (sourceIndex : Fin space.states.size)
    (sourceEq : space.states[sourceIndex] = source)
    (walk : task.Walk source target) :
    ∃ targetIndex : Fin space.states.size,
      space.states[targetIndex] = target := by
  rcases space.liftWalk sourceIndex sourceEq walk with
    ⟨targetIndex, _indexWalk, targetEq, _lengthEq⟩
  exact ⟨targetIndex, targetEq⟩

/-- Closure plus the represented root implies completeness for all walks. -/
theorem represents_reachable
    (space : FiniteStateSpace task)
    (target : State)
    (reachable : task.Reachable task.initial target) :
    ∃ targetIndex : Fin space.states.size,
      space.states[targetIndex] = target := by
  rcases reachable with ⟨walk⟩
  exact
    space.represents_walk space.root
      space.root_eq_initial walk

theorem toVertex_surjective (space : FiniteStateSpace task) :
    Function.Surjective space.toVertex := by
  intro vertex
  rcases space.represents_reachable vertex.1 vertex.2 with
    ⟨index, stateEq⟩
  refine ⟨index, ?_⟩
  apply Subtype.ext
  exact stateEq

/-- Array indices are equivalent to the complete semantic vertex space. -/
noncomputable def vertexEquiv (space : FiniteStateSpace task) :
    Fin space.states.size ≃ task.Vertex :=
  Equiv.ofBijective space.toVertex
    ⟨space.toVertex_injective, space.toVertex_surjective⟩

/-- Forget the finite index while preserving root, goals, and transitions. -/
def toTaskHom (space : FiniteStateSpace task) :
    Task.Hom space.indexTask task where
  mapState := fun index => space.states[index]
  mapAction := id
  map_initial := space.root_eq_initial
  map_goal := fun goal => goal
  map_step := fun step => step

/-- The canonical map between any two complete finite presentations. -/
noncomputable def mapIndex
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    (sourceSpace : FiniteStateSpace task)
    (targetSpace : FiniteStateSpace targetTask)
    (hom : Task.Hom task targetTask)
    (source : Fin sourceSpace.states.size) :
    Fin targetSpace.states.size :=
  targetSpace.vertexEquiv.symm
    (hom.mapVertex (sourceSpace.vertexEquiv source))

/-- Surjectivity on semantic vertices induces surjectivity on finite arrays. -/
theorem mapIndex_surjective
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    (sourceSpace : FiniteStateSpace task)
    (targetSpace : FiniteStateSpace targetTask)
    (hom : Task.Hom task targetTask)
    (surjective : Function.Surjective hom.mapVertex) :
    Function.Surjective
      (sourceSpace.mapIndex targetSpace hom) := by
  intro targetIndex
  rcases surjective (targetSpace.vertexEquiv targetIndex) with
    ⟨sourceVertex, sourceMaps⟩
  let sourceIndex := sourceSpace.vertexEquiv.symm sourceVertex
  refine ⟨sourceIndex, ?_⟩
  apply targetSpace.vertexEquiv.injective
  simp only [mapIndex, Equiv.apply_symm_apply]
  rw [show sourceSpace.vertexEquiv sourceIndex = sourceVertex by
    exact sourceSpace.vertexEquiv.apply_symm_apply sourceVertex]
  exact sourceMaps

@[simp] theorem mapIndex_state
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    (sourceSpace : FiniteStateSpace task)
    (targetSpace : FiniteStateSpace targetTask)
    (hom : Task.Hom task targetTask)
    (source : Fin sourceSpace.states.size) :
    targetSpace.states[
        sourceSpace.mapIndex targetSpace hom source] =
      hom.mapState sourceSpace.states[source] := by
  change
    (targetSpace.toVertex
      (sourceSpace.mapIndex targetSpace hom source)).1 =
      hom.mapState (sourceSpace.toVertex source).1
  exact congrArg Subtype.val
    (targetSpace.vertexEquiv.apply_symm_apply
      (hom.mapVertex (sourceSpace.vertexEquiv source)))

@[simp] theorem mapIndex_root
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    (sourceSpace : FiniteStateSpace task)
    (targetSpace : FiniteStateSpace targetTask)
    (hom : Task.Hom task targetTask) :
    sourceSpace.mapIndex targetSpace hom sourceSpace.root =
      targetSpace.root := by
  apply targetSpace.toVertex_injective
  apply Subtype.ext
  change
    targetSpace.states[
        sourceSpace.mapIndex targetSpace hom sourceSpace.root] =
      targetSpace.states[targetSpace.root]
  rw [mapIndex_state, sourceSpace.root_eq_initial,
    targetSpace.root_eq_initial, hom.map_initial]

/-- The induced map between finite index tasks. -/
noncomputable def indexHom
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    (sourceSpace : FiniteStateSpace task)
    (targetSpace : FiniteStateSpace targetTask)
    (hom : Task.Hom task targetTask) :
    Task.Hom sourceSpace.indexTask targetSpace.indexTask where
  mapState := sourceSpace.mapIndex targetSpace hom
  mapAction := hom.mapAction
  map_initial := sourceSpace.mapIndex_root targetSpace hom
  map_goal := by
    intro source sourceGoal
    change targetTask.goal
      targetSpace.states[sourceSpace.mapIndex targetSpace hom source]
    rw [mapIndex_state]
    exact hom.map_goal sourceGoal
  map_step := by
    intro source action target sourceStep
    change targetTask.step
      targetSpace.states[sourceSpace.mapIndex targetSpace hom source]
      (hom.mapAction action)
      targetSpace.states[sourceSpace.mapIndex targetSpace hom target]
    rw [mapIndex_state, mapIndex_state]
    exact hom.map_step sourceStep

/-- An array aligned with every vertex in a finite state-space presentation. -/
structure DistanceTable (space : FiniteStateSpace task) where
  values : Array Nat
  size_eq : values.size = space.states.size

namespace DistanceTable

def get (table : DistanceTable space)
    (index : Fin space.states.size) : Nat :=
  table.values[index.1]'(by
    rw [table.size_eq]
    exact index.2)

end DistanceTable

/--
A proof-facing BFS result. The mutable queue and hash table disappear here;
only the complete state space and the certified distance array remain.
-/
structure BfsCertificate (space : FiniteStateSpace task) where
  table : DistanceTable space
  certified :
    Task.RootedDistanceCertificate
      space.indexTask table.get

namespace BfsCertificate

theorem shortestWalkLength
    (certificate : BfsCertificate space)
    (target : Fin space.states.size) :
    space.indexTask.ShortestWalkLength
      space.root target (certificate.table.get target) :=
  certificate.certified.shortestWalkLength target

/-- Any simulation of complete spaces can only shorten root distance. -/
theorem mapIndex_distance_le
    {State' : Type u'} {Action' : Type v'}
    {targetTask : Task State' Action'}
    {sourceSpace : FiniteStateSpace task}
    {targetSpace : FiniteStateSpace targetTask}
    (sourceCertificate : BfsCertificate sourceSpace)
    (targetCertificate : BfsCertificate targetSpace)
    (hom : Task.Hom task targetTask)
    (source : Fin sourceSpace.states.size) :
    targetCertificate.table.get
        (sourceSpace.mapIndex targetSpace hom source) ≤
      sourceCertificate.table.get source := by
  rcases sourceCertificate.certified.exists_root_walk source with
    ⟨walk, walkLength⟩
  let mapped :=
    (sourceSpace.indexHom targetSpace hom).mapWalk walk
  have bound :=
    targetCertificate.certified.distance_le_walk_length mapped
  change
    targetCertificate.table.get
        (sourceSpace.mapIndex targetSpace hom source) ≤
      targetCertificate.table.get
          (sourceSpace.mapIndex targetSpace hom sourceSpace.root) +
        mapped.length at bound
  have mappedRoot :
      (sourceSpace.indexHom targetSpace hom).mapState
          sourceSpace.indexTask.initial =
        targetSpace.indexTask.initial :=
    (sourceSpace.indexHom targetSpace hom).map_initial
  have mappedRootDistance :
      targetCertificate.table.get
          ((sourceSpace.indexHom targetSpace hom).mapState
            sourceSpace.indexTask.initial) = 0 := by
    rw [mappedRoot]
    exact targetCertificate.certified.root_zero
  change
    targetCertificate.table.get
        (sourceSpace.mapIndex targetSpace hom sourceSpace.root) = 0
      at mappedRootDistance
  have mappedLength :
      mapped.length = sourceCertificate.table.get source :=
    ((sourceSpace.indexHom targetSpace hom).mapWalk_length walk).trans
      walkLength
  exact by omega

end BfsCertificate

/-- Reversibility and absence of self-loops turn a task into a simple graph. -/
structure SimpleGraphLaws (space : FiniteStateSpace task) : Prop where
  reverse :
    ∀ {source action target},
      space.indexTask.step source action target →
        ∃ reverseAction,
          space.indexTask.step target reverseAction source
  loopless :
    ∀ {state action}, ¬space.indexTask.step state action state

/-- The unlabelled finite graph underlying a complete task presentation. -/
def simpleGraph (space : FiniteStateSpace task)
    (laws : SimpleGraphLaws space) :
    SimpleGraph (Fin space.states.size) where
  Adj source target := space.indexTask.Moves source target
  symm := ⟨by
    rintro source target ⟨action, step⟩
    rcases laws.reverse step with ⟨reverseAction, reverseStep⟩
    exact ⟨reverseAction, reverseStep⟩⟩
  loopless := ⟨by
    rintro state ⟨action, step⟩
    exact laws.loopless step⟩

/-- A Mathlib bridge certificate on any state-space layer. -/
def IsBridge (space : FiniteStateSpace task)
    (laws : SimpleGraphLaws space)
    (source target : Fin space.states.size) : Prop :=
  (space.simpleGraph laws).IsBridge s(source, target)

/-- A vertex predicate disconnects two selected nodes after deletion. -/
def IsVertexCut (space : FiniteStateSpace task)
    (laws : SimpleGraphLaws space)
    (cut : Fin space.states.size → Prop)
    (source target : Fin space.states.size) : Prop :=
  ∀ (sourceOutside : ¬cut source) (targetOutside : ¬cut target),
    ¬((space.simpleGraph laws).induce {node | ¬cut node}).Reachable
      ⟨source, sourceOutside⟩
      ⟨target, targetOutside⟩

end FiniteStateSpace

namespace BisimulationQuotient

variable {State : Type u} {Action : Type v}
variable {task : Task State Action}

/-- The projection is onto the entire rooted reachable quotient space. -/
theorem mapVertex_surjective
    (quotient : BisimulationQuotient task) :
    Function.Surjective
      quotient.toObservation.projectionHom.mapVertex := by
  intro quotientVertex
  rcases quotientVertex.2 with ⟨quotientWalk⟩
  rcases quotient.liftTaskWalkWithLength
      quotientWalk task.initial rfl with
    ⟨target, concreteWalk, _lengthEq, targetClassEq⟩
  let concreteVertex : task.Vertex :=
    ⟨target, ⟨concreteWalk⟩⟩
  refine ⟨concreteVertex, ?_⟩
  apply Subtype.ext
  exact targetClassEq

/-- Every quotient-array node has a representative in any complete finer array. -/
theorem finite_mapIndex_surjective
    (quotient : BisimulationQuotient task)
    (sourceSpace : FiniteStateSpace task)
    (targetSpace :
      FiniteStateSpace quotient.toObservation.quotientTask) :
    Function.Surjective
      (sourceSpace.mapIndex targetSpace
        quotient.toObservation.projectionHom) :=
  sourceSpace.mapIndex_surjective targetSpace
    quotient.toObservation.projectionHom
    quotient.mapVertex_surjective

/--
Every quotient BFS distance is attained by at least one state in its concrete
fiber. Thus a quotient distance array is the fiberwise minimum of the finer
distance array, not an unrelated search result.
-/
theorem exists_fiber_distance_eq
    (quotient : BisimulationQuotient task)
    (sourceSpace : FiniteStateSpace task)
    (targetSpace :
      FiniteStateSpace quotient.toObservation.quotientTask)
    (sourceBfs : sourceSpace.BfsCertificate)
    (targetBfs : targetSpace.BfsCertificate)
    (targetIndex : Fin targetSpace.states.size) :
    ∃ sourceIndex : Fin sourceSpace.states.size,
      sourceSpace.mapIndex targetSpace
          quotient.toObservation.projectionHom sourceIndex =
        targetIndex ∧
      sourceBfs.table.get sourceIndex =
        targetBfs.table.get targetIndex := by
  rcases targetBfs.certified.exists_root_walk targetIndex with
    ⟨targetIndexWalk, targetIndexLength⟩
  let quotientWalk :=
    targetSpace.toTaskHom.mapWalk targetIndexWalk
  have quotientWalkLength :
      quotientWalk.length = targetBfs.table.get targetIndex :=
    (targetSpace.toTaskHom.mapWalk_length targetIndexWalk).trans
      targetIndexLength
  rcases quotient.liftTaskWalkWithLength
      quotientWalk task.initial
      targetSpace.root_eq_initial.symm with
    ⟨targetState, concreteWalk, concreteLength, targetClassEq⟩
  rcases sourceSpace.liftWalk
      sourceSpace.root sourceSpace.root_eq_initial concreteWalk with
    ⟨sourceIndex, sourceIndexWalk, sourceStateEq, sourceIndexLength⟩
  have sourceMaps :
      sourceSpace.mapIndex targetSpace
          quotient.toObservation.projectionHom sourceIndex =
        targetIndex := by
    apply targetSpace.toVertex_injective
    apply Subtype.ext
    change
      targetSpace.states[
          sourceSpace.mapIndex targetSpace
            quotient.toObservation.projectionHom sourceIndex] =
        targetSpace.states[targetIndex]
    rw [FiniteStateSpace.mapIndex_state, sourceStateEq]
    exact targetClassEq
  have sourceDistanceBound :=
    sourceBfs.certified.distance_le_walk_length sourceIndexWalk
  have sourceRootZero :
      sourceBfs.table.get sourceSpace.root = 0 :=
    sourceBfs.certified.root_zero
  rw [sourceRootZero, zero_add] at sourceDistanceBound
  have liftedLength :
      sourceIndexWalk.length = targetBfs.table.get targetIndex :=
    sourceIndexLength.trans
      (concreteLength.trans quotientWalkLength)
  have sourceLeTarget :
      sourceBfs.table.get sourceIndex ≤
        targetBfs.table.get targetIndex := by
    omega
  have targetLeSource :=
    sourceBfs.mapIndex_distance_le targetBfs
      quotient.toObservation.projectionHom sourceIndex
  have targetLeSource' :
      targetBfs.table.get targetIndex ≤
        sourceBfs.table.get sourceIndex := by
    simpa [sourceMaps] using targetLeSource
  exact
    ⟨sourceIndex, sourceMaps,
      Nat.le_antisymm sourceLeTarget targetLeSource'⟩

/-- A two-stage exact quotient tower, used for concrete/shape/mirror layers. -/
structure Tower (task : Task State Action) where
  first : BisimulationQuotient task
  second :
    BisimulationQuotient first.toObservation.quotientTask

namespace Tower

def middleTask (tower : Tower task) :=
  tower.first.toObservation.quotientTask

def topTask (tower : Tower task) :=
  tower.second.toObservation.quotientTask

theorem hasSolutionLength_iff_top
    (tower : Tower task) (distance : Nat) :
    task.HasSolutionLength distance ↔
      tower.topTask.HasSolutionLength distance :=
  (tower.first.hasSolutionLength_iff_quotient distance).trans
    (tower.second.hasSolutionLength_iff_quotient distance)

theorem shortestSolutionLength_iff_top
    (tower : Tower task) (distance : Nat) :
    task.ShortestSolutionLength distance ↔
      tower.topTask.ShortestSolutionLength distance :=
  (tower.first.shortestSolutionLength_iff_quotient distance).trans
    (tower.second.shortestSolutionLength_iff_quotient distance)

end Tower

end BisimulationQuotient

end StateSpace

namespace ClassicStateSpaceKernel

/-- The maintained concrete/shape/mirror state space as one quotient tower. -/
def symmetryTower :
    StateSpace.BisimulationQuotient.Tower concrete where
  first := concreteShapeQuotient
  second := shapeMirrorQuotient

theorem symmetryTower_shortestSolutionLength_116 :
    symmetryTower.topTask.ShortestSolutionLength 116 :=
  (symmetryTower.shortestSolutionLength_iff_top 116).mp
    concrete_shortestSolutionLength_116

/-- A vertex bottleneck proved on the mirror layer applies to concrete play. -/
theorem mirrorVertexSeparator_preimage
    {cut : MirrorShapeState → Prop}
    {source target : ValidClassicState}
    (separator :
      mirror.VertexSeparator cut
        (concreteToMirror.mapState source)
        (concreteToMirror.mapState target)) :
    concrete.VertexSeparator
      (fun state => cut (concreteToMirror.mapState state))
      source target :=
  concreteToMirror.vertexSeparator_preimage separator

/--
An edge bottleneck proved on the mirror graph pulls back to all concrete
labelled transitions represented by that quotient edge family.
-/
theorem mirrorEdgeSeparator_preimage
    {selected : MirrorShapeState → Unit → MirrorShapeState → Prop}
    {source target : ValidClassicState}
    (separator :
      mirror.EdgeSeparator selected
        (concreteToMirror.mapState source)
        (concreteToMirror.mapState target)) :
    concrete.EdgeSeparator
      (fun concreteSource action concreteTarget =>
        selected
          (concreteToMirror.mapState concreteSource)
          (concreteToMirror.mapAction action)
          (concreteToMirror.mapState concreteTarget))
      source target :=
  concreteToMirror.edgeSeparator_preimage separator

end ClassicStateSpaceKernel
end Huarongdao
