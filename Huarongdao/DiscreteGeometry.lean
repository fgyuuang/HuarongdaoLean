import Huarongdao.CaoProjection
import Huarongdao.StateSpaceAnalysis
import Huarongdao.GraphTopology
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace Huarongdao
namespace DiscreteGeometry

/-!
# Discrete geometry of Huarongdao state spaces

This module connects the maintained transition-system semantics to Mathlib's
graph metric, Hausdorff edistance, finite-dimensional inner-product spaces,
linear projections, and graph Laplacians.  The graph metric is extended-valued
on purpose: disconnected states have distance `∞` instead of a natural-number
junk value.
-/

open scoped BigOperators ENNReal InnerProductSpace

section GraphMetric

variable {V : Type*}

/-- The graph extended distance viewed in Mathlib's `ℝ≥0∞` codomain. -/
noncomputable def graphEDist (G : SimpleGraph V) (source target : V) : ℝ≥0∞ :=
  (G.edist source target : ℝ≥0∞)

@[simp] theorem graphEDist_self (G : SimpleGraph V) (source : V) :
    graphEDist G source source = 0 := by
  simp [graphEDist]

theorem graphEDist_comm (G : SimpleGraph V) (source target : V) :
    graphEDist G source target = graphEDist G target source := by
  simp [graphEDist, G.edist_comm]

theorem graphEDist_triangle (G : SimpleGraph V)
    (source middle target : V) :
    graphEDist G source target ≤
      graphEDist G source middle + graphEDist G middle target := by
  change (G.edist source target : ℝ≥0∞) ≤
    (G.edist source middle : ℝ≥0∞) +
      (G.edist middle target : ℝ≥0∞)
  simpa using ENat.toENNReal_mono G.edist_triangle

@[simp] theorem graphEDist_eq_zero_iff (G : SimpleGraph V)
    (source target : V) :
    graphEDist G source target = 0 ↔ source = target := by
  simp [graphEDist]

theorem graphEDist_eq_top_iff_not_reachable (G : SimpleGraph V)
    (source target : V) :
    graphEDist G source target = ⊤ ↔ ¬G.Reachable source target := by
  change (G.edist source target : ℝ≥0∞) = ⊤ ↔
    ¬G.Reachable source target
  simpa using (not_congr (SimpleGraph.edist_ne_top_iff_reachable
    (G := G) (u := source) (v := target)))

@[simp] theorem graphEDist_eq_one_iff_adj (G : SimpleGraph V)
    (source target : V) :
    graphEDist G source target = 1 ↔ G.Adj source target := by
  change (G.edist source target : ℝ≥0∞) = 1 ↔ G.Adj source target
  rw [← ENat.toENNReal_one]
  norm_cast
  exact SimpleGraph.edist_eq_one_iff_adj

/-- An extended metric space induced by a simple graph. -/
noncomputable def graphEMetricSpace (G : SimpleGraph V) : EMetricSpace V where
  toPseudoEMetricSpace :=
    PseudoEMetricSpace.ofEDist
      (graphEDist G)
      (graphEDist_self G)
      (graphEDist_comm G)
      (graphEDist_triangle G)
  eq_of_edist_eq_zero := by
    intro source target h
    exact (graphEDist_eq_zero_iff G source target).mp h

/-- Hausdorff edistance for subsets of a graph, with `∞` retained. -/
noncomputable def graphHausdorffEDist
    (G : SimpleGraph V) (source target : Set V) : ℝ≥0∞ :=
  letI := graphEMetricSpace G
  Metric.hausdorffEDist source target

theorem graphHausdorffEDist_comm
    (G : SimpleGraph V) (source target : Set V) :
    graphHausdorffEDist G source target =
      graphHausdorffEDist G target source := by
  letI : EMetricSpace V := graphEMetricSpace G
  change Metric.hausdorffEDist source target =
    Metric.hausdorffEDist target source
  exact Metric.hausdorffEDist_comm

theorem graphHausdorffEDist_triangle
    (G : SimpleGraph V) (source middle target : Set V) :
    graphHausdorffEDist G source target ≤
      graphHausdorffEDist G source middle +
        graphHausdorffEDist G middle target := by
  letI : EMetricSpace V := graphEMetricSpace G
  change Metric.hausdorffEDist source target ≤
    Metric.hausdorffEDist source middle +
      Metric.hausdorffEDist middle target
  exact Metric.hausdorffEDist_triangle

theorem graphHausdorffEDist_empty
    (G : SimpleGraph V) {source : Set V} (sourceNonempty : source.Nonempty) :
    graphHausdorffEDist G source ∅ = ⊤ := by
  letI : EMetricSpace V := graphEMetricSpace G
  change Metric.hausdorffEDist source ∅ = ⊤
  exact Metric.hausdorffEDist_empty sourceNonempty

end GraphMetric

section TaskGraph

open StateSpace

universe u v

variable {State : Type u} {Action : Type v}
variable (task : Task State Action) (reversible : task.Reversible)

/-- The simple graph on the rooted reachable vertices of a task. -/
def taskVertexGraph : SimpleGraph task.Vertex where
  Adj source target := (task.simpleGraph reversible).Adj source.1 target.1
  symm := ⟨by
    intro source target adjacent
    exact (task.simpleGraph reversible).adj_symm adjacent⟩
  loopless := ⟨by
    intro source adjacent
    exact (task.simpleGraph reversible).irrefl adjacent⟩

@[simp] theorem taskVertexGraph_adj
    (source target : task.Vertex) :
    (taskVertexGraph task reversible).Adj source target ↔
      (task.simpleGraph reversible).Adj source.1 target.1 :=
  Iff.rfl

noncomputable def taskVertexEDist
    (task : Task State Action) (reversible : task.Reversible)
    (source target : task.Vertex) : ℝ≥0∞ :=
  graphEDist (taskVertexGraph task reversible) source target

@[simp] theorem taskVertexEDist_self (source : task.Vertex) :
    taskVertexEDist task reversible source source = 0 :=
  graphEDist_self _ _

theorem taskVertexEDist_comm (source target : task.Vertex) :
    taskVertexEDist task reversible source target =
      taskVertexEDist task reversible target source :=
  graphEDist_comm _ _ _

theorem taskVertexEDist_eq_one_iff_adj
    (source target : task.Vertex) :
    taskVertexEDist task reversible source target = 1 ↔
      (taskVertexGraph task reversible).Adj source target :=
  graphEDist_eq_one_iff_adj _ _ _

theorem taskVertexEDist_eq_top_iff_not_reachable
    (source target : task.Vertex) :
    taskVertexEDist task reversible source target = ⊤ ↔
      ¬(taskVertexGraph task reversible).Reachable source target :=
  graphEDist_eq_top_iff_not_reachable _ _ _

end TaskGraph

section CaoFibers

open StateSpace
open ClassicStateSpaceKernel

/-- The concrete legal-state graph used by the Cao Cao fibre analysis. -/
def classicStateGraph : SimpleGraph ValidClassicState :=
  concrete.simpleGraph concreteReversible

/-- The fibre of the Cao Cao observation at a board coordinate. -/
def caoFiber (position : Pos) : Set ValidClassicState :=
  {state | caoPosition state = position}

@[simp] theorem mem_caoFiber
    (state : ValidClassicState) (position : Pos) :
    state ∈ caoFiber position ↔ caoPosition state = position :=
  Iff.rfl

/-- The extended Hausdorff distance between two Cao Cao position fibres. -/
noncomputable def caoFiberHausdorffEDist
    (source target : Pos) : ℝ≥0∞ :=
  graphHausdorffEDist classicStateGraph
    (caoFiber source) (caoFiber target)

theorem caoFiberHausdorffEDist_comm
    (source target : Pos) :
    caoFiberHausdorffEDist source target =
      caoFiberHausdorffEDist target source :=
  graphHausdorffEDist_comm _ _ _

theorem caoFiberHausdorffEDist_empty
    {source : Pos} (sourceNonempty : (caoFiber source).Nonempty) :
    graphHausdorffEDist classicStateGraph (caoFiber source) ∅ = ⊤ := by
  apply graphHausdorffEDist_empty _
  exact sourceNonempty

/-- A one-step edge changes the Cao Cao observation only when Cao Cao moved. -/
theorem caoFiber_edge_change_is_cao_move
    {source target : ValidClassicState} {action : Action}
    (step : concrete.step source action target)
    (different : caoPosition source ≠ caoPosition target) :
    action.piece = .caoCao :=
  action_eq_caoCao_of_caoPosition_ne step different

/-- Coordinate adjacency is weaker than adjacency in the legal state graph. -/
theorem caoPosition_adjacent_is_only_a_lower_bound
    {source target : ValidClassicState}
    {left right : Nat}
    (sourcePosition : caoPosition source = ⟨left, right⟩)
    (targetPosition : caoPosition target = ⟨left + 1, right⟩) :
    0 ≤ (classicStateGraph).edist source target := by
  exact bot_le

end CaoFibers

section FiniteFunctionSpace

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Ω]

/-- A finite state observable partitions the finite state function space. -/
abbrev StateFunctionSpace := EuclideanSpace ℝ ι

/-- The finite fibre of an observable at a state index. -/
def fibre (observe : ι → Ω) (source : ι) : Finset ι :=
  Finset.univ.filter fun target => observe target = observe source

@[simp] theorem mem_fibre (observe : ι → Ω) (source target : ι) :
    target ∈ fibre observe source ↔ observe target = observe source := by
  simp [fibre]

theorem source_mem_fibre (observe : ι → Ω) (source : ι) :
    source ∈ fibre observe source := by
  simp [fibre]

theorem fibre_nonempty (observe : ι → Ω) (source : ι) :
    (fibre observe source).Nonempty :=
  ⟨source, source_mem_fibre observe source⟩

def fibreSize (observe : ι → Ω) (source : ι) : Nat :=
  (fibre observe source).card

theorem fibreSize_pos (observe : ι → Ω) (source : ι) :
    0 < fibreSize observe source := by
  exact Finset.card_pos.mpr (fibre_nonempty observe source)

/-- The average of a real-valued function over the observable fibre. -/
noncomputable def fibreAverage (observe : ι → Ω)
    (f : StateFunctionSpace (ι := ι)) (source : ι) : ℝ :=
  (∑ target ∈ fibre observe source, f target) /
    (fibreSize observe source : ℝ)

/-- The explicit conditional-expectation operator associated to a finite
observable. -/
noncomputable def fibreProjectionFn (observe : ι → Ω) :
    StateFunctionSpace (ι := ι) → StateFunctionSpace (ι := ι) :=
  fun f => WithLp.toLp 2 (fun source => fibreAverage observe f source)

@[simp] theorem fibreProjectionFn_apply
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι)) (source : ι) :
    fibreProjectionFn observe f source = fibreAverage observe f source :=
  by
    simp [fibreProjectionFn]

@[simp] theorem fibreAverage_same_fibre
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι))
    {source target : ι}
    (same : observe source = observe target) :
    fibreAverage observe f source = fibreAverage observe f target := by
  unfold fibreAverage fibreSize
  have fibres :
      fibre observe source = fibre observe target := by
    ext candidate
    simp [same, eq_comm]
  rw [fibres]

theorem fibreProjectionFn_fibre_constant
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι))
    {source target : ι}
    (same : observe source = observe target) :
    fibreProjectionFn observe f source =
      fibreProjectionFn observe f target :=
  by
    simp only [fibreProjectionFn_apply]
    exact fibreAverage_same_fibre observe f same

theorem fibreProjectionFn_apply_of_fibreConstant
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι))
    (constant :
      ∀ source target, observe source = observe target →
        f source = f target)
    (source : ι) :
    fibreProjectionFn observe f source = f source := by
  rw [fibreProjectionFn_apply]
  unfold fibreAverage fibreSize
  have sum_eq :
      (∑ target ∈ fibre observe source, f target) =
        ∑ _target ∈ fibre observe source, f source := by
    apply Finset.sum_congr rfl
    intro target targetMem
    exact constant target source (by
      simpa [mem_fibre] using targetMem)
  rw [sum_eq, Finset.sum_const]
  simp only [nsmul_eq_mul]
  have denominator :
      (fibre observe source).card ≠ 0 := by
    exact Nat.ne_of_gt (fibreSize_pos observe source)
  have denominatorReal :
      (fibre observe source).card ≠ (0 : ℝ) := by
    exact_mod_cast denominator
  field_simp [denominatorReal]

theorem fibreProjectionFn_idempotent
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι)) :
    fibreProjectionFn observe (fibreProjectionFn observe f) =
      fibreProjectionFn observe f := by
  apply PiLp.ext
  intro source
  apply fibreProjectionFn_apply_of_fibreConstant
  intro left right same
  exact fibreProjectionFn_fibre_constant observe f same

/-- The subspace of functions constant on observable fibres. -/
def fibreConstantSubmodule (observe : ι → Ω) :
    Submodule ℝ (StateFunctionSpace (ι := ι)) where
  carrier := {f | ∀ source target, observe source = observe target →
    f source = f target}
  zero_mem' := by
    intro source target _
    simp
  add_mem' := by
    intro f g hf hg source target same
    simp [hf source target same, hg source target same]
  smul_mem' := by
    intro scalar f hf source target same
    simp [hf source target same]

theorem fibreProjectionFn_mem_fibreConstantSubmodule
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι)) :
    fibreProjectionFn observe f ∈ fibreConstantSubmodule observe :=
  by
    intro source target same
    exact fibreProjectionFn_fibre_constant observe f same

theorem fibreProjectionFn_eq_self_iff
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι)) :
    fibreProjectionFn observe f = f ↔
      f ∈ fibreConstantSubmodule observe := by
  constructor
  · intro equality source target same
    rw [← equality]
    exact fibreProjectionFn_fibre_constant observe f same
  · intro constant
    apply PiLp.ext
    intro source
    exact fibreProjectionFn_apply_of_fibreConstant
      observe f constant source

noncomputable def fibreProjectionLinearMap (observe : ι → Ω) :
    StateFunctionSpace (ι := ι) →ₗ[ℝ] StateFunctionSpace (ι := ι) where
  toFun := fibreProjectionFn observe
  map_add' := by
    intro f g
    apply PiLp.ext
    intro source
    simp [fibreProjectionFn, fibreAverage, Finset.sum_add_distrib, add_div]
  map_smul' := by
    intro scalar f
    apply PiLp.ext
    intro source
    simp only [fibreProjectionFn_apply, fibreAverage, PiLp.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [← mul_div_assoc, Finset.mul_sum]

theorem fibreProjectionLinearMap_apply
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι)) :
    fibreProjectionLinearMap observe f =
      fibreProjectionFn observe f :=
  rfl

theorem fibreProjectionLinearMap_idempotent
    (observe : ι → Ω) :
    IsIdempotentElem (fibreProjectionLinearMap observe) := by
  rw [isIdempotentElem_iff]
  apply LinearMap.ext
  intro f
  exact fibreProjectionFn_idempotent observe f

/-- The genuine Mathlib orthogonal projection onto the fibre-constant
subspace.  The explicit averaging map above is the computable candidate; this
object supplies the Hilbert-space projection with the Mathlib API. -/
noncomputable def fibreOrthogonalProjection (observe : ι → Ω) :
    StateFunctionSpace (ι := ι) →L[ℝ] StateFunctionSpace (ι := ι) :=
  (fibreConstantSubmodule observe).starProjection

@[simp] theorem fibreOrthogonalProjection_mem
    (observe : ι → Ω) (f : StateFunctionSpace (ι := ι)) :
    fibreOrthogonalProjection observe f ∈ fibreConstantSubmodule observe :=
  Submodule.starProjection_apply_mem _ _

@[simp] theorem fibreOrthogonalProjection_fixed
    (observe : ι → Ω) (f : fibreConstantSubmodule observe) :
    fibreOrthogonalProjection observe f = f :=
  Submodule.starProjection_mem_subspace_eq_self _

theorem fibreOrthogonalProjection_idempotent
    (observe : ι → Ω) :
    IsIdempotentElem (fibreOrthogonalProjection observe) :=
  Submodule.isIdempotentElem_starProjection _

end FiniteFunctionSpace

section Laplacian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real graph Laplacian matrix. -/
def graphLaplacian (G : SimpleGraph ι) [DecidableRel G.Adj] : Matrix ι ι ℝ :=
  G.lapMatrix ℝ

@[simp] theorem graphLaplacian_zero_iff_reachable_constant
    (G : SimpleGraph ι) [DecidableRel G.Adj] (f : ι → ℝ) :
    Matrix.mulVec (G.lapMatrix ℝ) f = 0 ↔
      ∀ source target, G.Reachable source target → f source = f target :=
  by
    simpa using
      (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable
        (G := G) (x := f))

theorem graphLaplacian_kernel_dimension_eq_components
    (G : SimpleGraph ι) [DecidableRel G.Adj] :
    Fintype.card G.ConnectedComponent =
      Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker :=
  by
    simpa using
      (SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix
        (G := G))

/-- A feature-induced similarity kernel on a finite state index set. -/
def featureSimilarity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (feature : ι → E) (source target : ι) : ℝ :=
  ⟪feature source, feature target⟫_ℝ

theorem featureSimilarity_comm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (feature : ι → E) (source target : ι) :
    featureSimilarity feature source target =
      featureSimilarity feature target source := by
  exact (real_inner_comm (feature source) (feature target)).symm

end Laplacian

section DiffusionAndResistance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuous-time heat kernel generated by the graph Laplacian. -/
noncomputable def graphHeatKernel
    (G : SimpleGraph ι) [DecidableRel G.Adj] (time : ℝ) : Matrix ι ι ℝ :=
  NormedSpace.exp (-time • G.lapMatrix ℝ)

@[simp] theorem graphHeatKernel_zero
    (G : SimpleGraph ι) [DecidableRel G.Adj] :
    graphHeatKernel G 0 = 1 := by
  simp [graphHeatKernel]

theorem graphHeatKernel_isSymm
    (G : SimpleGraph ι) [DecidableRel G.Adj] (time : ℝ) :
    (graphHeatKernel G time).IsSymm := by
  unfold graphHeatKernel
  exact (G.isSymm_lapMatrix ℝ).smul (-time) |>.exp

theorem graphHeatKernel_add
    (G : SimpleGraph ι) [DecidableRel G.Adj] (time₁ time₂ : ℝ) :
    graphHeatKernel G (time₁ + time₂) =
      graphHeatKernel G time₁ * graphHeatKernel G time₂ := by
  let L : Matrix ι ι ℝ := G.lapMatrix ℝ
  have commute :
      Commute (-time₁ • L) (-time₂ • L) := by
    exact ((Commute.refl L).smul_right (-time₂)).smul_left (-time₁)
  rw [graphHeatKernel, graphHeatKernel, graphHeatKernel]
  change NormedSpace.exp (-(time₁ + time₂) • L) =
    NormedSpace.exp (-time₁ • L) * NormedSpace.exp (-time₂ • L)
  rw [neg_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ commute

@[simp] theorem graphHeatKernel_transpose
    (G : SimpleGraph ι) [DecidableRel G.Adj] (time : ℝ) :
    Matrix.transpose (graphHeatKernel G time) = graphHeatKernel G time :=
  graphHeatKernel_isSymm G time

/-- The unit-conductance Dirichlet energy of a finite graph potential.

The double sum counts every undirected edge twice, hence the factor `1 / 2`.
The value is kept in `ℝ≥0∞` so it can participate in an extended-valued
variational definition when a terminal pair is disconnected. -/
noncomputable def graphDirichletEnergy
    (G : SimpleGraph ι) [DecidableRel G.Adj] (potential : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((∑ source : ι, ∑ target : ι,
      if G.Adj source target then
        (potential source - potential target) ^ 2
      else 0) / 2)

@[simp] theorem graphDirichletEnergy_nonneg
    (G : SimpleGraph ι) [DecidableRel G.Adj] (potential : ι → ℝ) :
    0 ≤ graphDirichletEnergy G potential :=
  bot_le

/-- The minimum Dirichlet energy required to maintain unit potential
difference between two terminals. -/
noncomputable def graphDirichletCapacity
    (G : SimpleGraph ι) [DecidableRel G.Adj] (source target : ι) : ℝ≥0∞ :=
  sInf {energy : ℝ≥0∞ |
    ∃ potential : ι → ℝ,
      potential source - potential target = 1 ∧
        energy = graphDirichletEnergy G potential}

/-- Extended effective resistance, with `∞` assigned to disconnected
terminals.  On a connected component it is the reciprocal of the
Dirichlet capacity. -/
noncomputable def graphEffectiveResistance
    (G : SimpleGraph ι) [DecidableRel G.Adj] (source target : ι) : ℝ≥0∞ :=
  if reachable : G.Reachable source target then
    (graphDirichletCapacity G source target)⁻¹
  else ⊤

@[simp] theorem graphEffectiveResistance_not_reachable
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    {source target : ι} (notReachable : ¬G.Reachable source target) :
    graphEffectiveResistance G source target = ⊤ := by
  simp [graphEffectiveResistance, notReachable]

@[simp] theorem graphEffectiveResistance_self
    (G : SimpleGraph ι) [DecidableRel G.Adj] (source : ι) :
    graphEffectiveResistance G source source = 0 := by
  have empty :
      {energy : ℝ≥0∞ |
        ∃ potential : ι → ℝ,
          potential source - potential source = 1 ∧
            energy = graphDirichletEnergy G potential} = ∅ := by
    ext energy
    simp
  simp [graphEffectiveResistance, graphDirichletCapacity, empty]

end DiffusionAndResistance

section CubicalRealization

universe u v

variable {State : Type u} {Action : Type v}
variable (task : StateSpace.Task State Action) (reversible : task.Reversible)

/-- The one-skeleton of the combinatorial geometric realization. -/
def oneSkeleton : SimpleGraph State :=
  task.simpleGraph reversible

/-- A square cell is represented by the proof-carrying boundary already used
by the local cubical theory. -/
abbrev SquareCell
    (task : StateSpace.Task State Action) (source : State) :=
  task.SquareBoundary source

/-- A finite combinatorial realization consists of a one-skeleton and chosen
commuting-action square cells.  The topological quotient can be built from
this data without changing the transition-system semantics. -/
structure Realization
    (task : StateSpace.Task State Action) (reversible : task.Reversible) where
  squareCells : State → Type (max u v)
  squareCell_source :
    ∀ source, Nonempty (squareCells source) →
      Nonempty (SquareCell task source)

def canonicalRealization : Realization task reversible where
  squareCells := fun source => SquareCell task source
  squareCell_source := by
    intro source cells
    exact cells

theorem squareCell_gives_closedWalk
    {source : State} (cell : SquareCell task source) :
    ∃ walk : task.ClosedWalk source, walk.length = 4 :=
  ⟨cell.walk, cell.walk_length⟩

theorem commuting_actions_give_squareCell
    (reversible : task.Reversible)
    {source : State} {first second : Action}
    (commutes : task.ActionsCommuteAt source first second) :
    Nonempty (SquareCell task source) :=
  StateSpace.Task.exists_square_boundary_data reversible commutes

/-- The fundamental loop quotient generated by immediate backtracks and
commuting squares.  This is the combinatorial one-dimensional/2-cell
interface; later work can identify it with a topological fundamental group. -/
abbrev FundamentalLoop
    (task : StateSpace.Task State Action) (reversible : task.Reversible)
    (source : State) :=
  task.FundamentalLoopClass reversible source

/-! A first-class two-dimensional combinatorial interface. -/

/-- A task square together with its base vertex. -/
abbrev TaskSquareCell
    (task : StateSpace.Task State Action) :=
  Σ source, SquareCell task source

noncomputable def taskSquareCells
    (task : StateSpace.Task State Action) (reversible : task.Reversible) :
    Type (max u v) :=
  TaskSquareCell task

def taskSquareBase
    (task : StateSpace.Task State Action)
    (cell : TaskSquareCell task) : State :=
  cell.1

def taskSquareBoundary
    (task : StateSpace.Task State Action)
    (cell : TaskSquareCell task) :
    task.ClosedWalk (taskSquareBase task cell) :=
  cell.2.walk

@[simp] theorem taskSquareBoundary_length
    (task : StateSpace.Task State Action)
    (cell : TaskSquareCell task) :
    (taskSquareBoundary task cell).length = 4 :=
  cell.2.walk_length

structure TwoDimensionalRealization
    (task : StateSpace.Task State Action) (reversible : task.Reversible) where
  vertices : Type u
  vertexEmbedding : vertices → State
  edges : SimpleGraph vertices
  cells : Type (max u v)
  cellBase : cells → vertices
  boundary : ∀ cell, task.ClosedWalk (vertexEmbedding (cellBase cell))
  boundary_length : ∀ cell, (boundary cell).length = 4

noncomputable def canonicalTwoDimensionalRealization :
    TwoDimensionalRealization task reversible where
  vertices := State
  vertexEmbedding := id
  edges := oneSkeleton task reversible
  cells := TaskSquareCell task
  cellBase := fun cell => cell.1
  boundary := fun cell => taskSquareBoundary task cell
  boundary_length := taskSquareBoundary_length task

end CubicalRealization

end DiscreteGeometry
end Huarongdao
