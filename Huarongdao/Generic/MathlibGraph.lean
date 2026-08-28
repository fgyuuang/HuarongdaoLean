import Huarongdao.Generic.Reversibility
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace SlidingPuzzle

/-- A vertex of the mathematical state graph is a valid puzzle state. Invalid
    raw arrays are excluded so that primitive moves form a symmetric relation. -/
abbrev PuzzleVertex (spec : PuzzleSpec) :=
  { state : State // ValidState spec state }

/-- The undirected, unlabelled graph obtained by forgetting which primitive
    action witnesses a transition between two valid puzzle states. -/
def puzzleSimpleGraph (spec : PuzzleSpec) :
    SimpleGraph (PuzzleVertex spec) where
  Adj source target := Step spec source.1 target.1
  symm := ⟨by
    intro source target step
    exact step_symm_of_valid source.property step⟩
  loopless := ⟨by
    intro state step
    exact step_irrefl spec state.1 step⟩

namespace Path

/-- Forget action labels in a certified puzzle path and obtain a mathlib walk.
    The source-validity hypothesis supplies the first subtype vertex; validity
    of every later vertex follows from successful execution. -/
def toSimpleGraphWalk :
    (path : Path spec source target) →
    (sourceValid : ValidState spec source) →
      (puzzleSimpleGraph spec).Walk
        ⟨source, sourceValid⟩
        ⟨target, path.target_valid sourceValid⟩
  | .nil _, _ => .nil
  | .cons action executed tail, sourceValid =>
      .cons ⟨action, executed⟩
        (toSimpleGraphWalk tail (tryMove_preserves_validity executed))

@[simp] theorem toSimpleGraphWalk_length
    (path : Path spec source target)
    (sourceValid : ValidState spec source) :
    (path.toSimpleGraphWalk sourceValid).length = path.length := by
  induction path with
  | nil => rfl
  | cons action executed tail ih =>
      change
        (toSimpleGraphWalk tail
          (tryMove_preserves_validity executed)).length + 1 =
          tail.length + 1
      rw [ih]

theorem toSimpleGraphReachable
    (path : Path spec source target)
    (sourceValid : ValidState spec source) :
    (puzzleSimpleGraph spec).Reachable
      ⟨source, sourceValid⟩
      ⟨target, path.target_valid sourceValid⟩ :=
  ⟨path.toSimpleGraphWalk sourceValid⟩

/-- The mathlib graph distance is a lower bound for the length of every
    certified primitive-action path with the same endpoints. -/
theorem simpleGraph_dist_le_length
    (path : Path spec source target)
    (sourceValid : ValidState spec source) :
    (puzzleSimpleGraph spec).dist
        ⟨source, sourceValid⟩
        ⟨target, path.target_valid sourceValid⟩ ≤
      path.length := by
  simpa using
    (puzzleSimpleGraph spec).dist_le
      (path.toSimpleGraphWalk sourceValid)

/-- A path is shortest between its fixed endpoints when no other certified
    primitive-action path between those endpoints is shorter. -/
def IsShortestTo (path : Path spec source target) : Prop :=
  ∀ other : Path spec source target, path.length ≤ other.length

/-- Equality with mathlib's graph distance proves endpoint-wise minimality. -/
theorem isShortestTo_of_length_eq_dist
    (candidate : Path spec source target)
    (sourceValid : ValidState spec source)
    (lengthEq :
      candidate.length =
        (puzzleSimpleGraph spec).dist
          ⟨source, sourceValid⟩
          ⟨target, candidate.target_valid sourceValid⟩) :
    candidate.IsShortestTo := by
  intro other
  rw [lengthEq]
  have lower := other.simpleGraph_dist_le_length sourceValid
  simpa using lower

/-- A path is shortest among paths from the same source to any goal state. -/
def IsShortestGoal (path : Path spec source target) : Prop :=
  goalMatches spec target = true ∧
  ∀ {otherTarget : State} (other : Path spec source otherTarget),
    goalMatches spec otherTarget = true →
    path.length ≤ other.length

end Path

/-- A lower bound on the graph distance from one valid source to every valid
    state satisfying the puzzle goal. -/
def GoalDistanceLowerBound
    (spec : PuzzleSpec) (source : PuzzleVertex spec) (bound : Nat) : Prop :=
  ∀ target : PuzzleVertex spec,
    goalMatches spec target.1 = true →
    bound ≤ (puzzleSimpleGraph spec).dist source target

/-- A goal path whose length is a lower bound on the distance to every goal is
    globally shortest among all certified goal paths from the same source. -/
theorem Path.isShortestGoal_of_distance_lower_bound
    (candidate : Path spec source target)
    (sourceValid : ValidState spec source)
    (candidateGoal : goalMatches spec target = true)
    (lowerBound :
      GoalDistanceLowerBound spec
        ⟨source, sourceValid⟩ candidate.length) :
    candidate.IsShortestGoal := by
  constructor
  · exact candidateGoal
  · intro otherTarget other otherGoal
    exact le_trans
      (lowerBound
        ⟨otherTarget, other.target_valid sourceValid⟩ otherGoal)
      (other.simpleGraph_dist_le_length sourceValid)

/-- Every project reachability proof has a compatible certified path, kept
    under `Nonempty` because `Reachable` is a proposition. -/
theorem reachable_nonempty_path
    (reachable : Reachable spec source target) :
    Nonempty (Path spec source target) := by
  induction reachable with
  | refl state =>
      exact ⟨.nil state⟩
  | tail step _ ih =>
      rcases step with ⟨action, executed⟩
      rcases ih with ⟨tail⟩
      exact ⟨.cons action executed tail⟩

/-- A mathlib walk yields project reachability after forgetting subtype proofs. -/
theorem reachable_of_simpleGraphWalk
    {source target : PuzzleVertex spec}
    (walk : (puzzleSimpleGraph spec).Walk source target) :
    Reachable spec source.1 target.1 := by
  induction walk with
  | nil =>
      exact Reachable.refl (spec := spec) _
  | cons step tail ih =>
      exact Reachable.tail (spec := spec) step ih

/-- Recover an action-labelled project path of exactly the same length as a
    mathlib walk. The result stays in `Prop`, so witnesses stored in `Step` may
    be safely unpacked. -/
theorem exists_path_of_simpleGraphWalk
    {source target : PuzzleVertex spec}
    (walk : (puzzleSimpleGraph spec).Walk source target) :
    ∃ path : Path spec source.1 target.1,
      path.length = walk.length := by
  induction walk with
  | nil =>
      exact ⟨.nil _, rfl⟩
  | cons step tail ih =>
      rcases step with ⟨action, executed⟩
      rcases ih with ⟨path, pathLength⟩
      exact ⟨.cons action executed path, by
        change path.length + 1 = tail.length + 1
        rw [pathLength]⟩

/-- Mathlib's existence theorem for a distance-realising walk can therefore
    be lifted back to an action-labelled project path without changing length. -/
theorem exists_path_length_eq_dist
    {source target : PuzzleVertex spec}
    (reachable : (puzzleSimpleGraph spec).Reachable source target) :
    ∃ path : Path spec source.1 target.1,
      path.length = (puzzleSimpleGraph spec).dist source target := by
  rcases reachable.exists_walk_length_eq_dist with ⟨walk, walkLength⟩
  rcases exists_path_of_simpleGraphWalk walk with ⟨path, pathLength⟩
  exact ⟨path, pathLength.trans walkLength⟩

/-- Project reachability and mathlib reachability agree on valid states. -/
theorem reachable_iff_simpleGraph
    (sourceValid : ValidState spec source)
    (targetValid : ValidState spec target) :
    Reachable spec source target ↔
      (puzzleSimpleGraph spec).Reachable
        ⟨source, sourceValid⟩
        ⟨target, targetValid⟩ := by
  constructor
  · intro reachable
    rcases reachable_nonempty_path reachable with ⟨path⟩
    simpa using path.toSimpleGraphReachable sourceValid
  · rintro ⟨walk⟩
    exact reachable_of_simpleGraphWalk walk

end SlidingPuzzle
