import Huarongdao.LocalTopology
import Huarongdao.StateSpaceAnalysis
import Huarongdao.StateSpaceConnectivity
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Huarongdao
namespace StateSpace

universe u v

namespace Task

variable {State : Type u} {Action : Type v}
variable {task : Task State Action}

/-- A two-colouring stated directly on the labelled transition system. -/
structure TwoColoring (task : Task State Action) where
  color : State → Bool
  flips :
    ∀ {source action target},
      task.step source action target → color source ≠ color target

namespace TwoColoring

/-- The two colour classes form a Mathlib bipartition of the task graph. -/
theorem isBipartiteWith
    (coloring : task.TwoColoring)
    (reversible : task.Reversible) :
    (task.simpleGraph reversible).IsBipartiteWith
      {state | coloring.color state = false}
      {state | coloring.color state = true} := by
  constructor
  · rw [Set.disjoint_left]
    intro state left right
    simp only [Set.mem_ofPred_eq] at left right
    simp [left] at right
  · intro source target adjacent
    rcases adjacent.1 with ⟨action, step⟩
    have different := coloring.flips step
    cases sourceColor : coloring.color source <;>
      cases targetColor : coloring.color target <;>
      simp_all

/-- Every reversible task carrying a step-flipping colour is bipartite. -/
theorem isBipartite
    (coloring : task.TwoColoring)
    (reversible : task.Reversible) :
    (task.simpleGraph reversible).IsBipartite :=
  (coloring.isBipartiteWith reversible).isBipartite

/-- Walk endpoints have the same colour exactly when the length is even. -/
theorem endpointColor_eq_iff_even
    (coloring : task.TwoColoring)
    (walk : task.Walk source target) :
    coloring.color source = coloring.color target ↔ Even walk.length := by
  induction walk with
  | nil => simp
  | @cons source middle target action first tail inductionHypothesis =>
      have firstDifferent := coloring.flips first
      cases sourceColor : coloring.color source <;>
        cases middleColor : coloring.color middle <;>
        cases targetColor : coloring.color target <;>
        simp_all [Walk.length, Nat.even_add_one]

/-- A closed walk in a two-coloured task has even length. -/
theorem closedWalk_even
    (coloring : task.TwoColoring)
    (walk : task.Walk source source) :
    Even walk.length :=
  (coloring.endpointColor_eq_iff_even walk).mp rfl

end TwoColoring

/--
A labelled cubical cell. Vertices are indexed by the Boolean `n`-cube and
every coordinate change from false to true is a semantic task transition.
Degenerate cells are allowed; `CubicalCell.Nondegenerate` excludes them.
-/
structure CubicalCell (task : Task State Action) (source : State) (n : Nat) where
  vertex : (Fin n → Bool) → State
  action : Fin n → Action
  origin : vertex (fun _ => false) = source
  edge :
    ∀ (bits : Fin n → Bool) (axis : Fin n),
      bits axis = false →
      task.step (vertex bits) (action axis)
        (vertex (Function.update bits axis true))

namespace CubicalCell

def Nondegenerate (cell : task.CubicalCell source n) : Prop :=
  Function.Injective cell.vertex

end CubicalCell

/-- The state supports an `n`-dimensional cubical direction family. -/
def SupportsCubeDimension
    (task : Task State Action) (source : State) (n : Nat) : Prop :=
  Nonempty (task.CubicalCell source n)

/-- The exact local cubical dimension is a maximal supported dimension. -/
def IsLocalCubicalDimension
    (task : Task State Action) (source : State) (n : Nat) : Prop :=
  task.SupportsCubeDimension source n ∧
    ∀ dimension,
      task.SupportsCubeDimension source dimension → dimension ≤ n

/-- Every commuting pair of actions supplies a two-dimensional cubical cell. -/
theorem supportsCubeDimension_two_of_commutes
    {source : State} {first second : Action}
    (commutes : task.ActionsCommuteAt source first second) :
    task.SupportsCubeDimension source 2 := by
  rcases commutes with
    ⟨afterFirst, afterSecond, opposite,
      firstStep, secondStep, firstThenSecond, secondThenFirst⟩
  refine ⟨{
    vertex := fun bits =>
      if bits 0 then
        if bits 1 then opposite else afterFirst
      else
        if bits 1 then afterSecond else source
    action := fun axis =>
      if axis = (0 : Fin 2) then first else second
    origin := by simp
    edge := ?_
  }⟩
  intro bits axis axisFalse
  fin_cases axis <;>
    cases firstBit : bits 0 <;>
    cases secondBit : bits 1 <;>
    simp_all [Function.update]

/-- A closed semantic walk based at one task state. -/
abbrev ClosedWalk (task : Task State Action) (base : State) :=
  task.Walk base base

/-- Proof-carrying boundary data for one commuting action square. -/
structure SquareBoundary
    (task : Task State Action) (source : State) where
  first : Action
  second : Action
  afterFirst : State
  afterSecond : State
  opposite : State
  reverseFirst : Action
  reverseSecond : Action
  firstStep : task.step source first afterFirst
  secondStep : task.step source second afterSecond
  firstThenSecond : task.step afterFirst second opposite
  oppositeToAfterSecond : task.step opposite reverseFirst afterSecond
  afterSecondToSource : task.step afterSecond reverseSecond source

namespace SquareBoundary

def walk (boundary : task.SquareBoundary source) : task.ClosedWalk source :=
  .cons boundary.first boundary.firstStep <|
    .cons boundary.second boundary.firstThenSecond <|
      .cons boundary.reverseFirst boundary.oppositeToAfterSecond <|
        .cons boundary.reverseSecond boundary.afterSecondToSource (.nil source)

@[simp] theorem walk_length (boundary : task.SquareBoundary source) :
    boundary.walk.length = 4 :=
  rfl

end SquareBoundary

/-- Every commuting action square has proof-carrying boundary data. -/
theorem exists_square_boundary_data
    (reversible : task.Reversible)
    {source : State} {first second : Action}
    (square : task.ActionsCommuteAt source first second) :
    Nonempty (task.SquareBoundary source) := by
  rcases square with
    ⟨afterFirst, afterSecond, target,
      firstStep, secondStep, firstThenSecond, secondThenFirst⟩
  rcases reversible.reverse_step secondThenFirst with
    ⟨reverseFirst, targetToAfterSecond⟩
  rcases reversible.reverse_step secondStep with
    ⟨reverseSecond, afterSecondToSource⟩
  exact ⟨{
    first := first
    second := second
    afterFirst := afterFirst
    afterSecond := afterSecond
    opposite := target
    reverseFirst := reverseFirst
    reverseSecond := reverseSecond
    firstStep := firstStep
    secondStep := secondStep
    firstThenSecond := firstThenSecond
    oppositeToAfterSecond := targetToAfterSecond
    afterSecondToSource := afterSecondToSource
  }⟩

/-- Every commuting action square gives a four-step closed walk. -/
theorem exists_square_boundary
    (reversible : task.Reversible)
    {source : State} {first second : Action}
    (square : task.ActionsCommuteAt source first second) :
    ∃ boundary : task.ClosedWalk source, boundary.length = 4 := by
  rcases exists_square_boundary_data reversible square with ⟨boundary⟩
  exact ⟨boundary.walk, boundary.walk_length⟩

/-- Proof-carrying data for an immediately reversible two-edge loop. -/
structure BacktrackBoundary
    (task : Task State Action) (source : State) where
  forward : Action
  backward : Action
  middle : State
  forwardStep : task.step source forward middle
  backwardStep : task.step middle backward source

namespace BacktrackBoundary

def walk (boundary : task.BacktrackBoundary source) : task.ClosedWalk source :=
  .cons boundary.forward boundary.forwardStep <|
    .cons boundary.backward boundary.backwardStep (.nil source)

@[simp] theorem walk_length (boundary : task.BacktrackBoundary source) :
    boundary.walk.length = 2 :=
  rfl

end BacktrackBoundary

/--
Elementary based-loop reductions. Context loops make the relation stable under
inserting or deleting a conjugated backtrack or commuting-square boundary.
-/
inductive ElementaryLoopHomotopy
    (reversible : task.Reversible) (base : State) :
    task.ClosedWalk base → task.ClosedWalk base → Prop where
  | eraseBacktrack
      (before after : task.ClosedWalk base)
      {point : State}
      (stem : task.Walk base point)
      (boundary : task.BacktrackBoundary point) :
      ElementaryLoopHomotopy reversible base
        (before.append
          ((stem.append
            (boundary.walk.append
              (reversible.reverseWalk stem))).append after))
        (before.append after)
  | eraseSquare
      (before after : task.ClosedWalk base)
      {point : State}
      (stem : task.Walk base point)
      (boundary : task.SquareBoundary point) :
      ElementaryLoopHomotopy reversible base
        (before.append
          ((stem.append
            (boundary.walk.append
              (reversible.reverseWalk stem))).append after))
        (before.append after)

/-- Equivalence closure generated by backtrack and square reductions. -/
def LoopHomotopySetoid
    (reversible : task.Reversible) (base : State) :
    Setoid (task.ClosedWalk base) :=
  Relation.EqvGen.setoid (task.ElementaryLoopHomotopy reversible base)

/--
Closed walks modulo the current cubical homotopy generators. This is the
underlying quotient type for a future combinatorial fundamental group.
-/
abbrev FundamentalLoopClass
    (reversible : task.Reversible) (base : State) :=
  Quotient (task.LoopHomotopySetoid reversible base)

end Task

namespace SimpleGraph

variable {Vertex : Type u} {graph : SimpleGraph Vertex}

namespace Walk

/-- A walk whose endpoint colours differ contains a colour-crossing edge. -/
theorem exists_crossing_edge
    (color : Vertex → Bool)
    (walk : graph.Walk source target)
    (different : color source ≠ color target) :
    ∃ left right,
      s(left, right) ∈ walk.edges ∧
      graph.Adj left right ∧
      color left ≠ color right := by
  induction walk with
  | nil => exact (different rfl).elim
  | @cons source middle target first tail inductionHypothesis =>
      by_cases firstCrosses : color source = color middle
      · rcases inductionHypothesis (fun equal =>
          different (firstCrosses.trans equal)) with
          ⟨left, right, member, adjacent, crosses⟩
        exact
          ⟨left, right, by simp [member], adjacent, crosses⟩
      · exact
          ⟨source, middle, by simp, first, firstCrosses⟩

end Walk

/--
A two-bank bridge certificate. Every edge crossing the banks must be the
selected edge. This is directly suitable for finite checker output.
-/
structure SideBridgeCertificate
    (graph : SimpleGraph Vertex) (source target : Vertex) where
  side : Vertex → Bool
  endpoints : side source ≠ side target
  uniqueCrossing :
    ∀ {left right},
      graph.Adj left right →
      side left ≠ side right →
      s(left, right) = s(source, target)

namespace SideBridgeCertificate

theorem isBridge
    (certificate : SideBridgeCertificate graph source target) :
    graph.IsBridge s(source, target) := by
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  intro walk
  rcases Walk.exists_crossing_edge
      certificate.side walk certificate.endpoints with
    ⟨left, right, member, adjacent, crosses⟩
  rw [certificate.uniqueCrossing adjacent crosses] at member
  exact member

end SideBridgeCertificate

/--
A two-bank vertex-gate certificate. Every edge crossing the banks touches the
selected gate predicate.
-/
structure SideVertexCertificate
    (graph : SimpleGraph Vertex) (gate : Vertex → Prop)
    (source target : Vertex) where
  side : Vertex → Bool
  endpoints : side source ≠ side target
  crossing :
    ∀ {left right},
      graph.Adj left right →
      side left ≠ side right →
      gate left ∨ gate right

namespace SideVertexCertificate

/-- Every source-target walk visits the certified gate. -/
theorem walk_hits
    (certificate : SideVertexCertificate graph gate source target)
    (walk : graph.Walk source target) :
    ∃ vertex ∈ walk.support, gate vertex := by
  rcases Walk.exists_crossing_edge
      certificate.side walk certificate.endpoints with
    ⟨left, right, member, adjacent, crosses⟩
  rcases certificate.crossing adjacent crosses with leftGate | rightGate
  · exact ⟨left, walk.fst_mem_support_of_mem_edges member, leftGate⟩
  · exact ⟨right, walk.snd_mem_support_of_mem_edges member, rightGate⟩

end SideVertexCertificate

end SimpleGraph

namespace FiniteStateSpace

variable {State : Type u} {Action : Type v}
variable {task : Task State Action}

/-- A Boolean label aligned with a complete finite state-space array. -/
structure BoolTable (space : FiniteStateSpace task) where
  values : Array Bool
  size_eq : values.size = space.states.size

namespace BoolTable

def get (table : BoolTable space)
    (index : Fin space.states.size) : Bool :=
  table.values[index.1]'(by
    rw [table.size_eq]
    exact index.2)

end BoolTable

namespace EdgeTable

def RespectsBridgeSides
    (side : BoolTable space)
    (source target : Fin space.states.size)
    (edge : Edge space) : Prop :=
  side.get edge.source = side.get edge.target ∨
    (edge.source = source ∧ edge.target = target) ∨
    (edge.source = target ∧ edge.target = source)

instance respectsBridgeSidesDecidable
    (side : BoolTable space)
    (source target : Fin space.states.size)
    (edge : Edge space) :
    Decidable (RespectsBridgeSides side source target edge) := by
  unfold RespectsBridgeSides
  infer_instance

/--
Check that the selected endpoints lie on different banks and every stored
labelled edge either stays inside one bank or is the selected bridge.
-/
def checkSideBridge
    (table : EdgeTable space)
    (side : BoolTable space)
    (source target : Fin space.states.size) : Bool :=
  decide (side.get source ≠ side.get target) &&
    table.edges.toList.all fun edge =>
      decide (RespectsBridgeSides side source target edge)

/-- A successful finite edge-table check yields a Mathlib bridge theorem. -/
theorem checkSideBridge_sound
    (table : EdgeTable space)
    (laws : SimpleGraphLaws space)
    (side : BoolTable space)
    (source target : Fin space.states.size)
    (checked : table.checkSideBridge side source target = true) :
    (space.simpleGraph laws).IsBridge s(source, target) := by
  have checks :
      decide (side.get source ≠ side.get target) = true ∧
      table.edges.toList.all (fun edge =>
        decide (RespectsBridgeSides side source target edge)) = true := by
    simpa only [checkSideBridge, Bool.and_eq_true] using checked
  have endpointCheck :
      decide (side.get source ≠ side.get target) = true :=
    checks.1
  have endpoints : side.get source ≠ side.get target :=
    of_decide_eq_true endpointCheck
  have edgeChecks :
      table.edges.toList.all (fun edge =>
        decide (RespectsBridgeSides side source target edge)) = true :=
    checks.2
  apply StateSpace.SimpleGraph.SideBridgeCertificate.isBridge
    {
      side := side.get
      endpoints := endpoints
      uniqueCrossing := ?_
    }
  intro left right adjacent crosses
  change space.indexTask.Moves left right at adjacent
  rcases adjacent with ⟨action, step⟩
  rcases table.complete step with
    ⟨edge, member, sourceEq, _actionEq, targetEq⟩
  have edgeChecked :
      decide (RespectsBridgeSides side source target edge) = true :=
    (List.all_eq_true.mp edgeChecks) edge member
  have respects : RespectsBridgeSides side source target edge :=
    of_decide_eq_true edgeChecked
  have edgeCrosses : side.get edge.source ≠ side.get edge.target := by
    simpa [sourceEq, targetEq] using crosses
  rcases respects with sameSide | forward | reverse
  · exact (edgeCrosses sameSide).elim
  · rcases forward with ⟨edgeSource, edgeTarget⟩
    rw [← sourceEq, ← targetEq, edgeSource, edgeTarget]
  · rcases reverse with ⟨edgeSource, edgeTarget⟩
    rw [← sourceEq, ← targetEq, edgeSource, edgeTarget]
    exact Sym2.eq_swap

def RespectsVertexGateSides
    (side gate : BoolTable space)
    (edge : Edge space) : Prop :=
  side.get edge.source = side.get edge.target ∨
    gate.get edge.source = true ∨
    gate.get edge.target = true

instance respectsVertexGateSidesDecidable
    (side gate : BoolTable space)
    (edge : Edge space) :
    Decidable (RespectsVertexGateSides side gate edge) := by
  unfold RespectsVertexGateSides
  infer_instance

/-- Check a source-target gate against every edge of an exact edge table. -/
def checkSideVertexGate
    (table : EdgeTable space)
    (side gate : BoolTable space)
    (source target : Fin space.states.size) : Bool :=
  decide (side.get source ≠ side.get target) &&
    table.edges.toList.all fun edge =>
      decide (RespectsVertexGateSides side gate edge)

/--
A successful finite gate check proves that every Mathlib walk between the
selected endpoints visits a vertex marked by the gate table.
-/
theorem checkSideVertexGate_sound
    (table : EdgeTable space)
    (laws : SimpleGraphLaws space)
    (side gate : BoolTable space)
    (source target : Fin space.states.size)
    (checked : table.checkSideVertexGate side gate source target = true) :
    ∀ walk : (space.simpleGraph laws).Walk source target,
      ∃ vertex ∈ walk.support, gate.get vertex = true := by
  have checks :
      decide (side.get source ≠ side.get target) = true ∧
      table.edges.toList.all (fun edge =>
        decide (RespectsVertexGateSides side gate edge)) = true := by
    simpa only [checkSideVertexGate, Bool.and_eq_true] using checked
  have endpoints : side.get source ≠ side.get target :=
    of_decide_eq_true checks.1
  let certificate :
      StateSpace.SimpleGraph.SideVertexCertificate
        (space.simpleGraph laws) (fun vertex => gate.get vertex = true)
        source target :=
    {
      side := side.get
      endpoints := endpoints
      crossing := by
        intro left right adjacent crosses
        change space.indexTask.Moves left right at adjacent
        rcases adjacent with ⟨action, step⟩
        rcases table.complete step with
          ⟨edge, member, sourceEq, _actionEq, targetEq⟩
        have edgeChecked :
            decide (RespectsVertexGateSides side gate edge) = true :=
          (List.all_eq_true.mp checks.2) edge member
        have respects : RespectsVertexGateSides side gate edge :=
          of_decide_eq_true edgeChecked
        have edgeCrosses :
            side.get edge.source ≠ side.get edge.target := by
          simpa [sourceEq, targetEq] using crosses
        rcases respects with sameSide | sourceGate | targetGate
        · exact (edgeCrosses sameSide).elim
        · left
          simpa [sourceEq] using sourceGate
        · right
          simpa [targetEq] using targetGate
    }
  exact certificate.walk_hits

end EdgeTable
end FiniteStateSpace

end StateSpace
end Huarongdao
