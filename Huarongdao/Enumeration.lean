import Huarongdao.Model

namespace Huarongdao

theorem Piece.mem_all (p : Piece) : p ∈ Piece.all := by
  cases p <;> simp [Piece.all]

theorem Direction.mem_all (d : Direction) : d ∈ Direction.all := by
  cases d <;> simp [Direction.all]

/-- Exact executable specification of the legal move enumerator. -/
theorem mem_legalMoves_iff {s : State} {p : Piece} {d : Direction} {t : State} :
    (p, d, t) ∈ legalMoves s ↔ tryMove s p d = some t := by
  constructor
  · intro h
    simp [legalMoves, List.mem_flatMap, List.mem_filterMap] at h
    rcases h with ⟨p', _hp, d', _hd, t', hm, hp, hd, ht⟩
    subst p'; subst d'; subst t'
    exact hm
  · intro hm
    simp [legalMoves, List.mem_flatMap, List.mem_filterMap]
    exact ⟨p, p.mem_all, d, d.mem_all, t, hm, rfl, rfl, rfl⟩

/-- Every triple emitted by legalMoves is a successful tryMove. -/
theorem legalMoves_sound {s : State} {p : Piece} {d : Direction} {t : State}
    (h : (p, d, t) ∈ legalMoves s) : tryMove s p d = some t :=
  mem_legalMoves_iff.mp h

/-- Every successful tryMove occurs in legalMoves. -/
theorem legalMoves_complete {s : State} {p : Piece} {d : Direction} {t : State}
    (h : tryMove s p d = some t) : (p, d, t) ∈ legalMoves s :=
  mem_legalMoves_iff.mpr h

end Huarongdao
