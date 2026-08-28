import Huarongdao.Generic.MathlibGraph
import Huarongdao.Generic.Certificates
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.List.Nodup
import Std.Tactic

namespace SlidingPuzzle

namespace GraphMetric

/-- A root-based natural-number labelling with exactly the local properties
    needed to certify graph distance. This separates shortest-path proof from
    the algorithm that computed the labels. -/
structure RootedDistanceCertificate {V : Type*}
    (graph : SimpleGraph V) (root : V) (rank : V → Nat) : Prop where
  root_zero : rank root = 0
  step :
    ∀ {source target : V}, graph.Adj source target →
      rank target ≤ rank source + 1
  predecessor :
    ∀ vertex, vertex ≠ root →
      ∃ previous, graph.Adj previous vertex ∧
        rank vertex = rank previous + 1

namespace RootedDistanceCertificate

theorem rank_le_walk_length
    {V : Type*} {graph : SimpleGraph V} {root source target : V}
    {rank : V → Nat}
    (certificate : RootedDistanceCertificate graph root rank)
    (walk : graph.Walk source target) :
    rank target ≤ rank source + walk.length := by
  induction walk with
  | nil => simp
  | cons adjacent tail ih =>
      have firstStep := certificate.step adjacent
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- Following certified predecessors constructs a root walk whose length is
    exactly the supplied rank. -/
theorem exists_root_walk
    {V : Type*} {graph : SimpleGraph V} {root : V} {rank : V → Nat}
    (certificate : RootedDistanceCertificate graph root rank)
    (vertex : V) :
    ∃ walk : graph.Walk root vertex, walk.length = rank vertex := by
  have build :
      ∀ distance vertex, rank vertex = distance →
        ∃ walk : graph.Walk root vertex, walk.length = rank vertex := by
    intro distance
    induction distance using Nat.strong_induction_on with
    | h distance ih =>
        intro vertex rankEq
        by_cases atRoot : vertex = root
        · subst vertex
          exact ⟨.nil, by simp [certificate.root_zero]⟩
        · rcases certificate.predecessor vertex atRoot with
            ⟨previous, adjacent, predecessorRank⟩
          have previousLt : rank previous < distance := by
            omega
          rcases ih (rank previous) previousLt previous rfl with
            ⟨walk, walkLength⟩
          exact ⟨walk.concat adjacent, by
            simp [walkLength, predecessorRank]⟩
  exact build (rank vertex) vertex rfl

theorem reachable
    {V : Type*} {graph : SimpleGraph V} {root : V} {rank : V → Nat}
    (certificate : RootedDistanceCertificate graph root rank)
    (vertex : V) :
    graph.Reachable root vertex := by
  rcases certificate.exists_root_walk vertex with ⟨walk, _⟩
  exact ⟨walk⟩

/-- The local step and predecessor conditions are sufficient to identify the
    rank with Mathlib's shortest-walk distance from the root. -/
theorem dist_eq_rank
    {V : Type*} {graph : SimpleGraph V} {root : V} {rank : V → Nat}
    (certificate : RootedDistanceCertificate graph root rank)
    (vertex : V) :
    graph.dist root vertex = rank vertex := by
  apply Nat.le_antisymm
  · rcases certificate.exists_root_walk vertex with ⟨walk, walkLength⟩
    simpa [walkLength] using graph.dist_le walk
  · rcases (certificate.reachable vertex).exists_walk_length_eq_dist with
      ⟨walk, walkLength⟩
    have lower := certificate.rank_le_walk_length walk
    simpa [certificate.root_zero, walkLength] using lower

end RootedDistanceCertificate

/-- A state predicate is a source-target vertex cut when deleting every vertex
    satisfying it destroys reachability. This supports puzzle-level cuts such
    as "the horizontal Guan Yu piece is below Cao Cao", not only singleton
    articulation vertices. -/
def IsVertexPredicateCut {V : Type*}
    (graph : SimpleGraph V) (cut : V → Prop) (source target : V) : Prop :=
  ∀ (sourceOutside : ¬cut source) (targetOutside : ¬cut target),
    ¬(graph.induce {vertex | ¬cut vertex}).Reachable
      ⟨source, sourceOutside⟩
      ⟨target, targetOutside⟩

/-- A certified predicate cut intersects every source-target walk. This is the
    graph-theoretic form of a mandatory puzzle phase or bottleneck. -/
theorem IsVertexPredicateCut.walk_hits
    {V : Type*} {graph : SimpleGraph V} {cut : V → Prop}
    {source target : V}
    (certificate : IsVertexPredicateCut graph cut source target)
    (walk : graph.Walk source target) :
    ∃ vertex ∈ walk.support, cut vertex := by
  classical
  by_contra noHit
  have avoids : ∀ vertex ∈ walk.support, ¬cut vertex := by
    intro vertex member satisfies
    exact noHit ⟨vertex, member, satisfies⟩
  exact certificate
    (avoids source walk.start_mem_support)
    (avoids target walk.end_mem_support)
    ⟨walk.induce {vertex | ¬cut vertex} avoids⟩

/-- A singleton predicate cut is the source-target version of a mandatory
    vertex (a dominator in algorithmic terminology). -/
def IsMandatoryVertex {V : Type*}
    (graph : SimpleGraph V) (source target gate : V) : Prop :=
  IsVertexPredicateCut graph (· = gate) source target

theorem IsMandatoryVertex.mem_support
    {V : Type*} {graph : SimpleGraph V} {source target gate : V}
    (mandatory : IsMandatoryVertex graph source target gate)
    (walk : graph.Walk source target) :
    gate ∈ walk.support := by
  rcases mandatory.walk_hits walk with ⟨vertex, member, equalsGate⟩
  simpa [equalsGate] using member

end GraphMetric

namespace StateGraph

/-- Finite vertices are array indices, not raw states. This makes finiteness
    and the correspondence with exported JSON node identifiers explicit. -/
abbrev Vertex (graph : StateGraph) := Fin graph.states.size

/-- Proof that a finite state array is an injective family of valid puzzle
    vertices and contains the designated initial-state root. -/
structure FiniteGraphCertificate
    (spec : PuzzleSpec) (graph : StateGraph) where
  root : graph.Vertex
  root_eq_initial : graph.states[root] = spec.initial
  valid :
    ∀ vertex : graph.Vertex, ValidState spec graph.states[vertex]
  nodup : graph.states.toList.Nodup

namespace FiniteGraphCertificate

/-- The state stored at each finite array index, viewed as a valid vertex of
    the full mathematical puzzle graph. -/
def vertexEmbedding
    (certificate : FiniteGraphCertificate spec graph) :
    graph.Vertex ↪ PuzzleVertex spec where
  toFun vertex := ⟨graph.states[vertex], certificate.valid vertex⟩
  inj' := by
    intro left right equal
    apply Fin.ext
    apply (certificate.nodup.getElem_inj_iff).mp
    exact congrArg Subtype.val equal

@[simp] theorem vertexEmbedding_state
    (certificate : FiniteGraphCertificate spec graph)
    (vertex : graph.Vertex) :
    (certificate.vertexEmbedding vertex).1 = graph.states[vertex] := rfl

/-- The finite graph is the full semantic puzzle graph comapped along the
    certified array embedding. Its adjacency relation is therefore `Step` on
    exactly the states represented by the array. -/
def finiteSimpleGraph
    (certificate : FiniteGraphCertificate spec graph) :
    SimpleGraph graph.Vertex :=
  (puzzleSimpleGraph spec).comap certificate.vertexEmbedding

instance finiteSimpleGraphDecidableAdj
    (certificate : FiniteGraphCertificate spec graph) :
    DecidableRel certificate.finiteSimpleGraph.Adj := by
  unfold finiteSimpleGraph
  infer_instance

@[simp] theorem finiteSimpleGraph_adj
    (certificate : FiniteGraphCertificate spec graph)
    (source target : graph.Vertex) :
    certificate.finiteSimpleGraph.Adj source target ↔
      Step spec graph.states[source] graph.states[target] := by
  rfl

/-- The index graph is isomorphic to the induced subgraph of the full puzzle
    graph on the certified finite state set. -/
noncomputable def isoInducedRange
    (certificate : FiniteGraphCertificate spec graph) :
    certificate.finiteSimpleGraph ≃g
      (puzzleSimpleGraph spec).induce
        (Set.range certificate.vertexEmbedding) :=
  (SimpleGraph.Embedding.comap certificate.vertexEmbedding
    (puzzleSimpleGraph spec)).isoInduceRange

@[simp] theorem isoInducedRange_apply_val
    (certificate : FiniteGraphCertificate spec graph)
    (vertex : graph.Vertex) :
    (certificate.isoInducedRange vertex).1 =
      certificate.vertexEmbedding vertex := rfl

@[simp] theorem root_embedding_state
    (certificate : FiniteGraphCertificate spec graph) :
    (certificate.vertexEmbedding certificate.root).1 = spec.initial := by
  exact certificate.root_eq_initial

/-- Membership in the exported state array is exactly membership in the range
    of the certified embedding into the complete semantic graph. -/
theorem mem_range_vertexEmbedding_iff
    (certificate : FiniteGraphCertificate spec graph)
    (state : PuzzleVertex spec) :
    state ∈ Set.range certificate.vertexEmbedding ↔
      state.1 ∈ graph.states.toList := by
  constructor
  · rintro ⟨vertex, rfl⟩
    exact List.getElem_mem _
  · intro member
    obtain ⟨index, bound, indexed⟩ := List.getElem_of_mem member
    let vertex : graph.Vertex := ⟨index, by simpa using bound⟩
    refine ⟨vertex, Subtype.ext ?_⟩
    change graph.states[index] = state.1
    exact (Array.getElem_toList bound).symm.trans indexed

end FiniteGraphCertificate

/-- Closure is strong enough to keep every vertex of a semantic walk inside
    the finite state array, provided its first vertex is already present. -/
theorem ClosedUnderMoves.simpleGraphWalk_support_mem
    {spec : PuzzleSpec} {graph : StateGraph}
    (closed : graph.ClosedUnderMoves spec)
    {source target : PuzzleVertex spec}
    (sourceMem : source.1 ∈ graph.states.toList)
    (walk : (puzzleSimpleGraph spec).Walk source target) :
    ∀ vertex ∈ walk.support, vertex.1 ∈ graph.states.toList := by
  induction walk with
  | nil =>
      simpa using sourceMem
  | @cons source middle target adjacent tail inductionHypothesis =>
      have middleMem : middle.1 ∈ graph.states.toList := by
        rcases adjacent with ⟨action, executed⟩
        exact closed.2 sourceMem executed
      intro vertex member
      rw [SimpleGraph.Walk.support_cons] at member
      cases member with
      | head =>
          exact sourceMem
      | tail _ tailMember =>
          exact inductionHypothesis middleMem vertex tailMember

/-- A total distance array indexed by the same finite vertex type as the state
    array. The size equality prevents `getD` fallback values from entering a
    shortest-path theorem. -/
structure DistanceTable (graph : StateGraph) : Prop where
  size_eq : graph.distance.size = graph.states.size

namespace DistanceTable

def get (table : DistanceTable graph) (vertex : graph.Vertex) : Nat :=
  graph.distance[vertex.1]'(by
    simp [table.size_eq, vertex.2])

end DistanceTable

/-- A proof-facing interface for a BFS result. The implementation may use
    mutable arrays, hash maps and parent pointers; only these semantic facts
    are consumed by the kernel-level distance proof. -/
structure BfsDistanceCertificate
    (spec : PuzzleSpec) (graph : StateGraph) where
  finite : FiniteGraphCertificate spec graph
  distances : DistanceTable graph
  root_distance : distances.get finite.root = 0
  step :
    ∀ {source target : graph.Vertex},
      finite.finiteSimpleGraph.Adj source target →
        distances.get target ≤ distances.get source + 1
  predecessor :
    ∀ vertex, vertex ≠ finite.root →
      ∃ previous,
        finite.finiteSimpleGraph.Adj previous vertex ∧
          distances.get vertex = distances.get previous + 1

namespace BfsDistanceCertificate

theorem rootedDistanceCertificate
    (certificate : BfsDistanceCertificate spec graph) :
    GraphMetric.RootedDistanceCertificate
      certificate.finite.finiteSimpleGraph
      certificate.finite.root
      certificate.distances.get where
  root_zero := certificate.root_distance
  step := certificate.step
  predecessor := certificate.predecessor

/-- The exported BFS distance at every certified state equals Mathlib's
    shortest-walk distance in the finite semantic state graph. -/
theorem finiteSimpleGraph_dist_eq_arrayDistance
    (certificate : BfsDistanceCertificate spec graph)
    (vertex : graph.Vertex) :
    certificate.finite.finiteSimpleGraph.dist
        certificate.finite.root vertex =
      certificate.distances.get vertex :=
  certificate.rootedDistanceCertificate.dist_eq_rank vertex

/-- A closed finite BFS presentation has the same distance as the unrestricted
    semantic puzzle graph. No shortest route can leave the exported state set:
    closure lifts every unrestricted walk to the induced finite subgraph. -/
theorem puzzleSimpleGraph_dist_eq_finiteSimpleGraph_dist
    (certificate : BfsDistanceCertificate spec graph)
    (closed : graph.ClosedUnderMoves spec)
    (vertex : graph.Vertex) :
    (puzzleSimpleGraph spec).dist
        (certificate.finite.vertexEmbedding certificate.finite.root)
        (certificate.finite.vertexEmbedding vertex) =
      certificate.finite.finiteSimpleGraph.dist
        certificate.finite.root vertex := by
  apply Nat.le_antisymm
  · rcases
        (certificate.rootedDistanceCertificate.reachable vertex)
          |>.exists_walk_length_eq_dist with
      ⟨finiteWalk, finiteLength⟩
    let inducedWalk :=
      finiteWalk.map certificate.finite.isoInducedRange.toHom
    let fullWalk :=
      inducedWalk.map
        (SimpleGraph.Embedding.induce
          (Set.range certificate.finite.vertexEmbedding)).toHom
    calc
      (puzzleSimpleGraph spec).dist
          (certificate.finite.vertexEmbedding certificate.finite.root)
          (certificate.finite.vertexEmbedding vertex) ≤
        fullWalk.length := by
          simpa [fullWalk, inducedWalk] using
            (puzzleSimpleGraph spec).dist_le fullWalk
      _ = inducedWalk.length := by
          exact SimpleGraph.Walk.length_map _ _
      _ = finiteWalk.length := by
          exact SimpleGraph.Walk.length_map _ _
      _ = certificate.finite.finiteSimpleGraph.dist
          certificate.finite.root vertex := finiteLength
  · have rootMem :
        (certificate.finite.vertexEmbedding certificate.finite.root).1 ∈
          graph.states.toList := by
      exact List.getElem_mem _
    have finiteReachable :=
      certificate.rootedDistanceCertificate.reachable vertex
    rcases finiteReachable with ⟨finiteWalk⟩
    let inducedReachWalk :=
      finiteWalk.map certificate.finite.isoInducedRange.toHom
    let fullReachWalk :=
      inducedReachWalk.map
        (SimpleGraph.Embedding.induce
          (Set.range certificate.finite.vertexEmbedding)).toHom
    have fullReachable :
        (puzzleSimpleGraph spec).Reachable
          (certificate.finite.vertexEmbedding certificate.finite.root)
          (certificate.finite.vertexEmbedding vertex) := by
      exact ⟨by simpa [fullReachWalk, inducedReachWalk] using fullReachWalk⟩
    rcases fullReachable.exists_walk_length_eq_dist with
      ⟨fullWalk, fullLength⟩
    have supportInArray :=
      closed.simpleGraphWalk_support_mem rootMem fullWalk
    have supportInRange :
        ∀ state ∈ fullWalk.support,
          state ∈ Set.range certificate.finite.vertexEmbedding := by
      intro state member
      exact
        (certificate.finite.mem_range_vertexEmbedding_iff state).2
          (supportInArray state member)
    let inducedWalk :=
      fullWalk.induce
        (Set.range certificate.finite.vertexEmbedding) supportInRange
    have inducedLength : inducedWalk.length = fullWalk.length := by
      change
        (fullWalk.induce
          (Set.range certificate.finite.vertexEmbedding)
          supportInRange).length =
        fullWalk.length
      calc
        (fullWalk.induce
            (Set.range certificate.finite.vertexEmbedding)
            supportInRange).length =
          ((fullWalk.induce
              (Set.range certificate.finite.vertexEmbedding)
              supportInRange).map
            (SimpleGraph.Embedding.induce
              (Set.range certificate.finite.vertexEmbedding)).toHom).length := by
                exact (SimpleGraph.Walk.length_map _ _).symm
        _ = fullWalk.length := by
          exact congrArg SimpleGraph.Walk.length
            (SimpleGraph.Walk.map_induce fullWalk supportInRange)
    let liftedWalk :
        certificate.finite.finiteSimpleGraph.Walk
          certificate.finite.root vertex := by
      apply
        (inducedWalk.map
          certificate.finite.isoInducedRange.symm.toHom).copy
      · apply (certificate.finite.isoInducedRange.symm_apply_eq).2
        apply Subtype.ext
        rfl
      · apply (certificate.finite.isoInducedRange.symm_apply_eq).2
        apply Subtype.ext
        rfl
    calc
      certificate.finite.finiteSimpleGraph.dist
          certificate.finite.root vertex ≤
        liftedWalk.length :=
          certificate.finite.finiteSimpleGraph.dist_le liftedWalk
      _ = inducedWalk.length := by simp [liftedWalk]
      _ = fullWalk.length := inducedLength
      _ = (puzzleSimpleGraph spec).dist
          (certificate.finite.vertexEmbedding certificate.finite.root)
          (certificate.finite.vertexEmbedding vertex) := fullLength

/-- Consequently, a checked closure certificate upgrades the exported BFS
    labels from finite-graph distances to distances in the complete puzzle
    state graph. -/
theorem puzzleSimpleGraph_dist_eq_arrayDistance
    (certificate : BfsDistanceCertificate spec graph)
    (closed : graph.checkClosedGraph spec = true)
    (vertex : graph.Vertex) :
    (puzzleSimpleGraph spec).dist
        (certificate.finite.vertexEmbedding certificate.finite.root)
        (certificate.finite.vertexEmbedding vertex) =
      certificate.distances.get vertex := by
  rw [
    certificate.puzzleSimpleGraph_dist_eq_finiteSimpleGraph_dist
      (graph.checkClosedGraph_closed closed) vertex
  ]
  exact certificate.finiteSimpleGraph_dist_eq_arrayDistance vertex

end BfsDistanceCertificate

end StateGraph

end SlidingPuzzle
