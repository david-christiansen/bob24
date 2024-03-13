import Bob.List
import Bob.Array

theorem filter_go_spec {α} (p : α → Prop) [DecidablePred p] (out arr : Array α) (i : Nat) :
    (Bob.Array.filter.go p arr i out).toList = out.toList ++ Bob.List.filter p (arr.toList.drop i) := by
  unfold Bob.Array.filter.go
  split
  next hi =>
    have eq : arr.data[i] = arr[i] := rfl
    split
    next hp =>
      rw [filter_go_spec] -- induction happens here
      simp [Bob.List.filter, ← List.get_drop_eq_drop arr.data i, hi, hp, eq]
    next hnp =>
      rw [filter_go_spec] -- induction happens here
      simp [Bob.List.filter, ← List.get_drop_eq_drop arr.data i, hi, hnp, eq]
  next =>
    have : Array.size arr ≤ i := by omega
    simp [Bob.List.filter, List.drop_eq_nil_of_le, this]
termination_by arr.size - i

theorem filter_spec {α} (p : α → Prop) [DecidablePred p] (arr : Array α) :
    (Bob.Array.filter p arr).toList = Bob.List.filter p arr.toList := by
  unfold Bob.Array.filter
  rw [filter_go_spec]
  simp
