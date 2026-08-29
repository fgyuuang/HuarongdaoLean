import Huarongdao.ClassicFullSpaceCertificate
import Std.Data.HashSet.Lemmas
import Mathlib.Data.List.Nodup

set_option maxRecDepth 100000

namespace Huarongdao
namespace ClassicFullSpace

/-!
## Soundness of the executable key-uniqueness check

`uniqueKeys` is implemented as a tail-recursive scan of the generated list.
The native certificate only records the resulting boolean; the lemmas below
make the semantic bridge explicit, first for lists of keys and then for array
indices.
-/

theorem uniqueKeysList_sound
    (known : Std.HashSet String) (states : List State)
    (checked : uniqueKeysList known states = true) :
    (∀ key ∈ states.map State.key, key ∉ known) ∧
      (states.map State.key).Nodup := by
  induction states generalizing known with
  | nil =>
      simp
  | cons state states ih =>
      by_cases h : known.contains state.key = true
      · simp [uniqueKeysList, h] at checked
      · have hNot : state.key ∉ known := by
          intro member
          exact h ((Std.HashSet.mem_iff_contains).mp member)
        have tailChecked :
            uniqueKeysList (known.insert state.key) states = true := by
          simpa [uniqueKeysList, h] using checked
        have tail := ih (known.insert state.key) tailChecked
        constructor
        · intro key member
          simp only [List.map_cons, List.mem_cons] at member
          rcases member with rfl | member
          · exact hNot
          · intro keyKnown
            exact (tail.1 key member)
              (Std.HashSet.mem_insert.mpr (Or.inr keyKnown))
        · rw [List.map_cons, List.nodup_cons]
          constructor
          · intro member
            exact tail.1 state.key member
              (Std.HashSet.mem_insert_self)
          · exact tail.2

theorem uniqueKeys_list_nodup
    {states : Array State}
    (checked : uniqueKeys states = true) :
    (states.toList.map State.key).Nodup := by
  apply (uniqueKeysList_sound
    (known := (∅ : Std.HashSet String))
    (states := states.toList) ?_).2
  simpa [uniqueKeys] using checked

theorem state_injective_of_uniqueKeys
    {states : Array State}
    (checked : uniqueKeys states = true) :
    Function.Injective
      (fun index : Fin states.size => states[index]) := by
  have keyNodup := uniqueKeys_list_nodup checked
  intro left right stateEq
  apply Fin.ext
  have leftBound : left.1 < states.toList.length := by
    simpa using left.2
  have rightBound : right.1 < states.toList.length := by
    simpa using right.2
  have leftMapBound :
      left.1 < (states.toList.map State.key).length := by
    simpa using leftBound
  have rightMapBound :
      right.1 < (states.toList.map State.key).length := by
    simpa using rightBound
  apply (keyNodup.getElem_inj_iff
    (i := left.1) (j := right.1)
    (hi := leftMapBound) (hj := rightMapBound)).mp
  have leftValue := Array.getElem_toList (xs := states)
    (i := left.1) leftBound
  have rightValue := Array.getElem_toList (xs := states)
    (i := right.1) rightBound
  calc
    (states.toList.map State.key)[left.1] =
        (states.toList[left.1]).key := by
      simpa using (List.getElem_map State.key
        (l := states.toList) (i := left.1)
        (by simpa [List.length_map] using leftBound))
    _ = (states[left.1]).key := by
      exact congrArg State.key leftValue
    _ = (states[right.1]).key := congrArg State.key stateEq
    _ = (states.toList[right.1]).key := by
      exact congrArg State.key rightValue.symm
    _ = (states.toList.map State.key)[right.1] := by
      symm
      simpa using (List.getElem_map State.key
        (l := states.toList) (i := right.1)
        (by simpa [List.length_map] using rightBound))

/-- The already-certified native uniqueness fact yields the required
index-level injection without a second 65,880-by-65,880 computation. -/
theorem allShapeStates_state_injective :
    Function.Injective
      (fun index : Fin allShapeStates.size => allShapeStates[index]) := by
  have checked : uniqueKeys allShapeStates = true := by
    simpa [analyze] using analysis_keysUnique
  exact state_injective_of_uniqueKeys checked

end ClassicFullSpace
end Huarongdao
