import Huarongdao.ClassicFullSpaceCompleteness
import Std.Data.HashMap

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Fast canonical representatives

The executable state array stores the four vertical pieces and four soldiers in
row-major board order.  A legal move can temporarily permute those labels.
`canonicalState` restores the same order before an index lookup, so replay
checks compare arrays directly instead of searching all `4! * 4!` relabelings.
-/

def canonicalState (state : State) : State :=
  representativeState
    (state.pos .caoCao)
    (state.pos .guanYu)
    (boardSort (verticalPositions state))
    (boardSort (soldierPositions state))

theorem canonicalState_sameShape (state : State) :
    SameShape state (canonicalState state) := by
  unfold canonicalState
  have verticalLength :
      (boardSort (verticalPositions state)).length = 4 := by
    have h := List.Perm.length_eq
      (boardSort_perm (verticalPositions state))
    simpa [verticalPositions] using h
  have soldierLength :
      (boardSort (soldierPositions state)).length = 4 := by
    have h := List.Perm.length_eq
      (boardSort_perm (soldierPositions state))
    simpa [soldierPositions] using h
  have representativeVertical :
      verticalPositions
        (representativeState
          (state.pos .caoCao) (state.pos .guanYu)
          (boardSort (verticalPositions state))
          (boardSort (soldierPositions state))) =
        boardSort (verticalPositions state) := by
    have helper :
        ∀ (vertical soldiers : List Pos),
          vertical.length = 4 →
          verticalPositions
              (representativeState
                (state.pos .caoCao) (state.pos .guanYu)
                vertical soldiers) = vertical := by
      intro vertical soldiers h
      cases vertical with
      | nil => simp at h
      | cons a rest =>
        cases rest with
        | nil => simp at h
        | cons b rest =>
          cases rest with
          | nil => simp at h
          | cons c rest =>
            cases rest with
            | nil => simp at h
            | cons d rest =>
              cases rest with
              | nil => rfl
              | cons e rest => simp at h
    exact helper _ _ verticalLength
  have representativeSoldier :
      soldierPositions
        (representativeState
          (state.pos .caoCao) (state.pos .guanYu)
          (boardSort (verticalPositions state))
          (boardSort (soldierPositions state))) =
        boardSort (soldierPositions state) := by
    have helper :
        ∀ (vertical soldiers : List Pos),
          soldiers.length = 4 →
          soldierPositions
              (representativeState
                (state.pos .caoCao) (state.pos .guanYu)
                vertical soldiers) = soldiers := by
      intro vertical soldiers h
      cases soldiers with
      | nil => simp at h
      | cons a rest =>
        cases rest with
        | nil => simp at h
        | cons b rest =>
          cases rest with
          | nil => simp at h
          | cons c rest =>
            cases rest with
            | nil => simp at h
            | cons d rest =>
              cases rest with
              | nil => rfl
              | cons e rest => simp at h
    exact helper _ _ soldierLength
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [representativeVertical]
    exact (boardSort_perm _).symm
  · rw [representativeSoldier]
    exact (boardSort_perm _).symm

/-- Look up the canonicalized state and require exact array equality with the
candidate.  The equality test is a cheap final guard against malformed
indices; the soundness theorem below does not trust the hash key. -/
def canonicalRepresentation
    (states : Array State) (index : Std.HashMap String Nat)
    (state : State) : Option Nat :=
  match index[(canonicalState state).key]? with
  | some target =>
      if target < states.size &&
          canonicalState state == states.getD target classic then
        some target
      else
        none
  | none => none

theorem canonicalRepresentation_sound
    {states : Array State} {index : Std.HashMap String Nat}
    {state : State} {target : Nat}
    (h : canonicalRepresentation states index state = some target) :
    target < states.size ∧
      SameShape state (states.getD target classic) := by
  cases keyLookup : index[(canonicalState state).key]? with
  | none =>
      simp [canonicalRepresentation, keyLookup] at h
  | some candidate =>
      simp only [canonicalRepresentation, keyLookup] at h
      have hcond :
          (candidate < states.size ∧
            canonicalState state = states.getD candidate classic) ∧
            candidate = target := by
        simpa [Bool.and_eq_true, beq_iff_eq] using h
      have targetBound : target < states.size := by
        simpa [hcond.2] using hcond.1.1
      refine ⟨targetBound, ?_⟩
      rw [← hcond.2, ← hcond.1.2]
      exact canonicalState_sameShape state

end ClassicFullSpace
end Huarongdao
