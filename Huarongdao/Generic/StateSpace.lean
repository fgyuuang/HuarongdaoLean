import Huarongdao.StateSpace
import Huarongdao.Generic.Paths

namespace SlidingPuzzle

/--
The canonical state-space semantics of an arbitrary sliding-puzzle
specification. The domain-specific `Path` and `Solution` types remain as
compatibility proof carriers and are equivalent to this task interface.
-/
def stateSpaceTask (spec : PuzzleSpec) :
    Huarongdao.StateSpace.Task State Action where
  initial := spec.initial
  goal := fun state => goalMatches spec state = true
  step := fun source action target =>
    tryMove spec source action.block action.direction = some target

/-- Convert a compatibility path to the canonical task walk. -/
def taskWalkOfPath :
    {source target : State} →
      Path spec source target →
      (stateSpaceTask spec).Walk source target
  | _, _, .nil state => .nil state
  | _, _, .cons action executed tail =>
      .cons action executed (taskWalkOfPath tail)

/-- Convert a canonical task walk back to a compatibility path. -/
def pathOfTaskWalk :
    {source target : State} →
      (stateSpaceTask spec).Walk source target →
      Path spec source target
  | _, _, .nil state => .nil state
  | _, _, .cons action executed tail =>
      .cons action executed (pathOfTaskWalk tail)

@[simp] theorem pathOfTaskWalk_taskWalkOfPath
    (path : Path spec source target) :
    pathOfTaskWalk (taskWalkOfPath path) = path := by
  induction path with
  | nil => rfl
  | cons action executed tail ih =>
      simp [taskWalkOfPath, pathOfTaskWalk, ih]

@[simp] theorem taskWalkOfPath_pathOfTaskWalk
    (walk : (stateSpaceTask spec).Walk source target) :
    taskWalkOfPath (pathOfTaskWalk walk) = walk := by
  induction walk with
  | nil => rfl
  | cons action executed tail ih =>
      simp [taskWalkOfPath, pathOfTaskWalk, ih]

@[simp] theorem taskWalkOfPath_actions
    (path : Path spec source target) :
    (taskWalkOfPath path).actions = path.actions := by
  induction path with
  | nil => rfl
  | cons action executed tail ih =>
      simp [taskWalkOfPath, Huarongdao.StateSpace.Task.Walk.actions,
        Path.actions, ih]

@[simp] theorem taskWalkOfPath_length
    (path : Path spec source target) :
    (taskWalkOfPath path).length = path.length := by
  induction path with
  | nil => rfl
  | cons action executed tail ih =>
      simp [taskWalkOfPath, Huarongdao.StateSpace.Task.Walk.length,
        Path.length, ih]

@[simp] theorem pathOfTaskWalk_actions
    (walk : (stateSpaceTask spec).Walk source target) :
    (pathOfTaskWalk walk).actions = walk.actions := by
  rw [← taskWalkOfPath_actions (pathOfTaskWalk walk)]
  simp

@[simp] theorem pathOfTaskWalk_length
    (walk : (stateSpaceTask spec).Walk source target) :
    (pathOfTaskWalk walk).length = walk.length := by
  rw [← taskWalkOfPath_length (pathOfTaskWalk walk)]
  simp

/-- Convert a compatibility solution to the canonical task solution. -/
def taskSolutionOfSolution (solution : Solution spec) :
    (stateSpaceTask spec).Solution where
  target := solution.target
  walk := taskWalkOfPath solution.path
  solved := solution.solved

/-- Recover a compatibility solution from a canonical task solution. -/
def solutionOfTaskSolution
    (solution : (stateSpaceTask spec).Solution) :
    Solution spec where
  target := solution.target
  path := pathOfTaskWalk solution.walk
  solved := solution.solved

@[simp] theorem solutionOfTaskSolution_taskSolutionOfSolution
    (solution : Solution spec) :
    solutionOfTaskSolution (taskSolutionOfSolution solution) = solution := by
  cases solution with
  | mk target path solved =>
      rw [Solution.mk.injEq]
      exact ⟨rfl, heq_of_eq (pathOfTaskWalk_taskWalkOfPath path)⟩

@[simp] theorem taskSolutionOfSolution_solutionOfTaskSolution
    (solution : (stateSpaceTask spec).Solution) :
    taskSolutionOfSolution (solutionOfTaskSolution solution) = solution := by
  cases solution with
  | mk target walk solved =>
      rw [Huarongdao.StateSpace.Task.Solution.mk.injEq]
      exact ⟨rfl, heq_of_eq (taskWalkOfPath_pathOfTaskWalk walk)⟩

@[simp] theorem taskSolutionOfSolution_actions
    (solution : Solution spec) :
    (taskSolutionOfSolution solution).actions = solution.path.actions :=
  taskWalkOfPath_actions solution.path

@[simp] theorem taskSolutionOfSolution_length
    (solution : Solution spec) :
    (taskSolutionOfSolution solution).length = solution.path.length :=
  taskWalkOfPath_length solution.path

@[simp] theorem solutionOfTaskSolution_actions
    (solution : (stateSpaceTask spec).Solution) :
    (solutionOfTaskSolution solution).path.actions = solution.actions :=
  pathOfTaskWalk_actions solution.walk

@[simp] theorem solutionOfTaskSolution_length
    (solution : (stateSpaceTask spec).Solution) :
    (solutionOfTaskSolution solution).path.length = solution.length :=
  pathOfTaskWalk_length solution.walk

end SlidingPuzzle
