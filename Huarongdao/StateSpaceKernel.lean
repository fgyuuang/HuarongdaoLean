import Huarongdao.CorridorCompression
import Huarongdao.StateSpaceSymmetry
import Huarongdao.Generic.Transition

namespace Huarongdao

/-!
The maintained public mathematical state-space API.

Import this module when developing mathematical results about Huarongdao state
spaces. `StateSpace.Task` remains the single semantic kernel. This module
collects the maintained classic instances, compatibility adapters, exact
quotients, group actions, and weighted corridor interface in one place.

The unrestricted classic task named `raw` exists only as the compatibility
target of the original `Path` and `Solution` types. The mathematical
abstraction tower starts at `concrete`, whose states carry legality proofs.
-/
namespace ClassicStateSpaceKernel

/-- The unrestricted classic task used by the original path API. -/
abbrev raw : StateSpace.Task State Action :=
  StateSpace.classicTask

/-- Legal labelled boards and exact piece-labelled moves. -/
def concrete : StateSpace.Task ValidClassicState Action :=
  validClassicTask

/-- Equal-shaped labels identified, with one quotient edge per concrete move. -/
def shape : StateSpace.Task ShapeState Unit :=
  shapeGraphTask

/-- Equal-shape states additionally identified under horizontal reflection. -/
def mirror : StateSpace.Task MirrorShapeState Unit :=
  mirrorShapeTask

/-- Mirror states with forced non-branching corridors represented as weighted macros. -/
def corridor : StateSpace.Task CorridorState Nat :=
  corridorTask

/-- Exact equal-shape observation on legal labelled states. -/
def concreteShapeObservation : StateSpace.Observation concrete :=
  shapeObservation

/-- Representative-wise exactness of the equal-shape quotient. -/
def concreteShapeQuotient :
    StateSpace.BisimulationQuotient concrete :=
  shapeBisimulation

/-- Exact horizontal-reflection observation on equal-shape states. -/
def shapeMirrorObservation : StateSpace.Observation shape :=
  mirrorShapeObservation

/-- Representative-wise exactness of the horizontal mirror quotient. -/
def shapeMirrorQuotient :
    StateSpace.BisimulationQuotient shape :=
  mirrorShapeBisimulation

/-- Equal-shape relabelings presented as a group action on concrete states. -/
def equalShapeSymmetry :
    StateSpace.SymmetryAction concrete :=
  equalShapeRelabelingAction

/-- Horizontal reflection presented as a two-element group action. -/
def horizontalSymmetry :
    StateSpace.SymmetryAction shape :=
  horizontalMirrorAction

/-- The relabeling action orbits are exactly the maintained equal-shape classes. -/
theorem equalShapeOrbit_iff
    (source target : ValidClassicState) :
    equalShapeSymmetry.OrbitEquiv source target ↔
      SameShape source.1 target.1 :=
  relabelingOrbitEquiv_iff_sameShape source target

/-- The reflection action orbits are exactly the maintained mirror classes. -/
theorem horizontalOrbit_iff
    (source target : ShapeState) :
    horizontalSymmetry.OrbitEquiv source target ↔
      ShapeMirrorEquiv source target :=
  horizontalOrbitEquiv_iff_shapeMirrorEquiv source target

/-- Canonical projection from concrete labelled states to equal-shape classes. -/
def concreteToShape : StateSpace.Task.Hom concrete shape :=
  concreteShapeObservation.projectionHom

/-- Canonical projection from equal-shape classes to horizontal-mirror classes. -/
def shapeToMirror : StateSpace.Task.Hom shape mirror :=
  shapeMirrorObservation.projectionHom

/-- The composed two-stage quotient projection. -/
def concreteToMirror : StateSpace.Task.Hom concrete mirror :=
  shapeToMirror.comp concreteToShape

/-- Convert an original classic path to the canonical raw-task walk. -/
def walkOfPath :
    {source target : State} → Path source target → raw.Walk source target :=
  StateSpace.classicWalkOfPath

/-- Convert a canonical raw-task walk to the original classic path type. -/
def pathOfWalk :
    {source target : State} → raw.Walk source target → Path source target :=
  StateSpace.pathOfClassicWalk

@[simp] theorem pathOfWalk_walkOfPath (path : Path source target) :
    pathOfWalk (walkOfPath path) = path :=
  StateSpace.pathOfClassicWalk_classicWalkOfPath path

@[simp] theorem walkOfPath_pathOfWalk (walk : raw.Walk source target) :
    walkOfPath (pathOfWalk walk) = walk :=
  StateSpace.classicWalkOfPath_pathOfClassicWalk walk

@[simp] theorem walkOfPath_length (path : Path source target) :
    (walkOfPath path).length = path.length :=
  StateSpace.classicWalkOfPath_length path

@[simp] theorem pathOfWalk_length (walk : raw.Walk source target) :
    (pathOfWalk walk).length = walk.length :=
  StateSpace.pathOfClassicWalk_length walk

/-- Original classic reachability is equivalent to canonical task reachability. -/
theorem rawReachable_iff :
    raw.Reachable source target ↔ Huarongdao.Reachable source target :=
  StateSpace.classicTask_reachable_iff

/-- Convert an original classic solution to the canonical raw-task solution. -/
def rawSolutionOfSolution
    (solution : Huarongdao.Solution classic) :
    raw.Solution :=
  StateSpace.classicTaskSolutionOfSolution solution

/-- Convert a canonical raw-task solution to the original solution type. -/
def solutionOfRawSolution
    (solution : raw.Solution) :
    Huarongdao.Solution classic :=
  StateSpace.solutionOfClassicTaskSolution solution

@[simp] theorem solutionOfRawSolution_rawSolutionOfSolution
    (solution : Huarongdao.Solution classic) :
    solutionOfRawSolution (rawSolutionOfSolution solution) = solution :=
  StateSpace.solutionOfClassicTaskSolution_classicTaskSolutionOfSolution
    solution

@[simp] theorem rawSolutionOfSolution_solutionOfRawSolution
    (solution : raw.Solution) :
    rawSolutionOfSolution (solutionOfRawSolution solution) = solution :=
  StateSpace.classicTaskSolutionOfSolution_solutionOfClassicTaskSolution
    solution

theorem rawSolution_minimal_iff
    (solution : Huarongdao.Solution classic) :
    (rawSolutionOfSolution solution).Minimal ↔ solution.Minimal :=
  StateSpace.classicTaskSolution_minimal_iff solution

/-- Concrete walks project through both exact quotient layers without changing length. -/
theorem concreteWalk_projectsToMirror
    (walk : concrete.Walk source target) :
    (concreteToMirror.mapWalk walk).length = walk.length :=
  concreteToMirror.mapWalk_length walk

/-- Primitive cost of a corridor walk, rather than its number of macro edges. -/
def corridorCost (walk : corridor.Walk source target) : Nat :=
  corridorWalkCost walk

/--
A reduced mirror walk equipped with its anchor segmentation compresses to the
maintained corridor task without changing primitive cost.
-/
theorem segmentedMirrorWalk_compresses
    (walk : MirrorShapeWalk source.1 target.1)
    (segmented : CorridorSegmentationOf walk) :
    ∃ compressed : corridor.Walk source target,
      corridorCost compressed = walk.length :=
  corridorWalk_compressWithCost walk segmented

/--
Every weighted corridor walk expands through both quotient layers to a
concrete valid-state walk whose primitive length is the sum of macro weights.
-/
theorem corridorWalk_liftsToConcrete
    (walk : corridor.Walk source target)
    (sourceRepresentative : ValidClassicState)
    (source_eq :
      MirrorShapeState.ofState sourceRepresentative = source.1) :
    ∃ targetRepresentative,
      ∃ concreteWalk : concrete.Walk
          sourceRepresentative targetRepresentative,
        concreteWalk.length = corridorCost walk ∧
        MirrorShapeState.ofState targetRepresentative = target.1 :=
  corridorWalk_liftToConcreteWithCost walk sourceRepresentative source_eq

/-- Goal predicates agree at the concrete representative and mirror quotient. -/
theorem mirrorGoal_ofState_iff (state : ValidClassicState) :
    mirror.goal (MirrorShapeState.ofState state) ↔
      concrete.goal state :=
  Iff.rfl

/-- Goal predicates agree between a corridor anchor and its mirror node. -/
theorem corridorGoal_iff_mirror (state : CorridorState) :
    corridor.goal state ↔ mirror.goal state.1 :=
  Iff.rfl

end ClassicStateSpaceKernel

end Huarongdao

namespace SlidingPuzzle

/-!
The maintained arbitrary-puzzle entry point. The domain-specific path objects
are compatibility proof carriers; `StateSpaceKernel.task` is the canonical
mathematical transition system.
-/
namespace StateSpaceKernel

/-- Canonical state-space task associated with an arbitrary puzzle specification. -/
abbrev task (spec : PuzzleSpec) :
    Huarongdao.StateSpace.Task State Action :=
  stateSpaceTask spec

/-- Convert a compatibility path to the canonical task walk. -/
def walkOfPath :
    {source target : State} →
      Path spec source target → (task spec).Walk source target :=
  taskWalkOfPath

/-- Convert a canonical task walk back to a compatibility path. -/
def pathOfWalk :
    {source target : State} →
      (task spec).Walk source target → Path spec source target :=
  pathOfTaskWalk

@[simp] theorem pathOfWalk_walkOfPath
    (path : Path spec source target) :
    pathOfWalk (walkOfPath path) = path :=
  pathOfTaskWalk_taskWalkOfPath path

@[simp] theorem walkOfPath_pathOfWalk
    (walk : (task spec).Walk source target) :
    walkOfPath (pathOfWalk walk) = walk :=
  taskWalkOfPath_pathOfTaskWalk walk

@[simp] theorem walkOfPath_length
    (path : Path spec source target) :
    (walkOfPath path).length = path.length :=
  taskWalkOfPath_length path

@[simp] theorem pathOfWalk_length
    (walk : (task spec).Walk source target) :
    (pathOfWalk walk).length = walk.length :=
  pathOfTaskWalk_length walk

/-- Compatibility reachability and canonical task reachability coincide. -/
theorem reachable_iff :
    Reachable spec source target ↔
      (task spec).Reachable source target :=
  reachable_iff_taskReachable

/-- Convert a compatibility solution to the canonical task solution. -/
def taskSolutionOfSolution
    (solution : Solution spec) :
    (task spec).Solution :=
  SlidingPuzzle.taskSolutionOfSolution solution

/-- Convert a canonical task solution back to the compatibility type. -/
def solutionOfTaskSolution
    (solution : (task spec).Solution) :
    Solution spec :=
  SlidingPuzzle.solutionOfTaskSolution solution

@[simp] theorem solutionOfTaskSolution_taskSolutionOfSolution
    (solution : Solution spec) :
    solutionOfTaskSolution (taskSolutionOfSolution solution) = solution :=
  SlidingPuzzle.solutionOfTaskSolution_taskSolutionOfSolution solution

@[simp] theorem taskSolutionOfSolution_solutionOfTaskSolution
    (solution : (task spec).Solution) :
    taskSolutionOfSolution (solutionOfTaskSolution solution) = solution :=
  SlidingPuzzle.taskSolutionOfSolution_solutionOfTaskSolution solution

end StateSpaceKernel

end SlidingPuzzle
