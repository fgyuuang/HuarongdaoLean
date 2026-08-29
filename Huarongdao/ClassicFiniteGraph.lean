import Huarongdao.ClassicCertificate
import Mathlib.Combinatorics.SimpleGraph.Metric
import Std.Tactic

namespace Huarongdao

/-- A vertex of the finite classic quotient presentation is an array index. -/
abbrev ClassicQuotientVertex (graph : Graph) := Fin graph.states.size

/-- `QStep` between two states is witnessed by a legal move whose target is
    equal-shape equivalent to the displayed representative. -/
theorem QStep_iff_exists_legalMove {s t : State} :
    QStep s t ↔ ∃ move ∈ legalMoves s, SameShape move.2.2 t := by
  constructor
  · rintro ⟨p, d, next, executed, equivalent⟩
    exact ⟨(p, d, next), legalMoves_complete executed, equivalent⟩
  · rintro ⟨move, member, equivalent⟩
    exact ⟨move.1, move.2.1, move.2.2, legalMoves_sound member, equivalent⟩

namespace ClassicQuotientGraphCertificate

/-- The finite equal-shape quotient graph as a Mathlib `SimpleGraph`.  Every
    adjacency is a non-loop quotient step, and reversibility comes from the
    primitive move inverse transported through the equal-shape class. -/
def classicQuotientSimpleGraph
    (certificate : ClassicQuotientGraphCertificate graph) :
    SimpleGraph (ClassicQuotientVertex graph) where
  Adj source target :=
    source ≠ target ∧ QStep graph.states[source] graph.states[target]
  symm := by
    intro source target adjacent
    exact ⟨adjacent.1.symm,
      qstep_symm_of_valid
        (certificate.valid source) (certificate.valid target) adjacent.2⟩
  loopless := by
    intro vertex self
    exact self.1 rfl

@[simp] theorem classicQuotientSimpleGraph_adj
    (certificate : ClassicQuotientGraphCertificate graph)
    (source target : ClassicQuotientVertex graph) :
    certificate.classicQuotientSimpleGraph.Adj source target ↔
      source ≠ target ∧ QStep graph.states[source] graph.states[target] := by
  rfl

/-- Executable adjacency test for the finite quotient graph. -/
def classicQuotientAdjBool
    (certificate : ClassicQuotientGraphCertificate graph)
    (source target : ClassicQuotientVertex graph) : Bool :=
  decide (source ≠ target) &&
    (legalMoves (graph.states[source])).any fun move =>
      decide (SameShape move.2.2 (graph.states[target]))

theorem classicQuotientAdjBool_iff
    (certificate : ClassicQuotientGraphCertificate graph)
    (source target : ClassicQuotientVertex graph) :
    classicQuotientAdjBool certificate source target = true ↔
      certificate.classicQuotientSimpleGraph.Adj source target := by
  constructor
  · intro checked
    rw [classicQuotientAdjBool, Bool.and_eq_true] at checked
    rcases checked with ⟨distinct, moves⟩
    rw [List.any_eq_true] at moves
    rcases moves with ⟨move, member, sameShape⟩
    exact ⟨of_decide_eq_true distinct,
      (QStep_iff_exists_legalMove.mpr
        ⟨move, member, of_decide_eq_true sameShape⟩)⟩
  · intro adjacent
    rcases adjacent with ⟨distinct, step⟩
    rw [classicQuotientAdjBool, Bool.and_eq_true]
    constructor
    · exact by simp [distinct]
    · rw [List.any_eq_true]
      rcases (QStep_iff_exists_legalMove.mp step) with ⟨move, member, sameShape⟩
      exact ⟨move, member, by simp [sameShape]⟩

instance classicQuotientSimpleGraphDecidableAdj
    (certificate : ClassicQuotientGraphCertificate graph) :
    DecidableRel certificate.classicQuotientSimpleGraph.Adj := by
  intro source target
  exact decidable_of_iff
    (classicQuotientAdjBool certificate source target = true)
    (classicQuotientAdjBool_iff certificate source target)

end ClassicQuotientGraphCertificate

/-- The complete classic quotient graph, ready for Mathlib graph-theoretic
    analysis. -/
def classicFiniteQuotientSimpleGraph :
    SimpleGraph (ClassicQuotientVertex classicQuotientGraph) :=
  classicQuotientGraphCertificate.classicQuotientSimpleGraph

instance classicFiniteQuotientSimpleGraphDecidableAdj :
    DecidableRel classicFiniteQuotientSimpleGraph.Adj := by
  unfold classicFiniteQuotientSimpleGraph
  infer_instance

end Huarongdao
