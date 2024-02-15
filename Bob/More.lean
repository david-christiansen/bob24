import Std

def insertSorted [inst : LE α] [DecidableRel inst.le] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i'+1, isLt⟩ =>
    have : i' < arr.size := by omega
    if arr[i'] ≤ arr[i] then
      arr
    else
      insertSorted (arr.swap ⟨i', by assumption⟩ i) ⟨i', by simp [*] ⟩


namespace Pairwise

def Sorted [LE α] (arr : Array α) : Prop :=
  ∀ i, (h : i < arr.size) → i = 0 ∨ arr[i - 1]'(by omega) ≤ arr[i]

def SortedUntil [LE α] (arr : Array α) (stop : Nat) : Prop :=
  ∀ i, (h : i < stop ∧ i < arr.size) → i = 0 ∨ arr[i - 1]'(by omega) ≤ arr[i]'(by omega)

section

variable [inst : LE α]

theorem sorted_until_all (arr : Array α) : SortedUntil arr arr.size ↔ Sorted arr := by
  unfold Sorted
  unfold SortedUntil
  constructor
  . intro h i hi
    apply h; trivial
  . intro h i hi
    apply h

theorem empty_sorted (arr : Array α) : SortedUntil arr 0 := by
  unfold SortedUntil
  intro i h
  cases h
  contradiction

theorem singleton_sorted (arr : Array α) : SortedUntil arr 1 := by
  unfold SortedUntil
  intro i h
  left
  omega


theorem prev_sorted (arr : Array α) : SortedUntil arr (n + 1) → SortedUntil arr n := by
  intro h
  intro i hi
  apply h
  omega

theorem insertSorted_size  [DecidableRel inst.le] (i : Nat) (arr : Array α) (isLt : i < arr.size) (size : Nat) :  arr.size = size → (insertSorted arr ⟨i, isLt⟩).size = size:= by
  intro hEq
  induction i generalizing arr with
  | zero => simp [insertSorted, *]
  | succ n ih =>
    simp only [insertSorted]
    split <;> simp [ih, *]

@[simp]
theorem insertSorted_size' [DecidableRel inst.le] (i : Nat) (arr : Array α) (isLt : i < arr.size) :  arr.size = (insertSorted arr ⟨i, isLt⟩).size := by
  rw [insertSorted_size i arr isLt arr.size]
  rfl

theorem insertSorted_no_swap_after [DecidableRel inst.le] (i j : Fin arr.size) : i < j → (@insertSorted _ inst _ arr i)[j]'(by cases j; rw [← insertSorted_size']; assumption ) = arr[j] := by
  intro h
  let ⟨i, _⟩ := i
  induction i
  . simp [insertSorted]
  . simp [insertSorted]
    cases


theorem insertSorted_sorted_no_swap [DecidableRel inst.le]
    (i : Nat) (arr : Array α) (isLt : i < arr.size)
    : arr[i - 1]'(by omega) ≤ arr[i] → SortedUntil arr i →
      SortedUntil arr (i + 1) := by
  intro hle hSorted
  intro n hn
  by_cases eq : n = i
  . right
    subst eq
    assumption
  . have : n < i := by omega
    apply hSorted
    constructor
    . assumption
    . omega


theorem insertSorted_swap_end (i : Nat) (arr : Array α) (isLt : i+1 < arr.size) : SortedUntil arr i → SortedUntil (arr.swap ⟨i, by omega⟩ ⟨i+1, by omega⟩) i := by sorry

theorem insertSorted_sorted [DecidableRel inst.le] (i : Nat) (arr : Array α) (isLt : i < arr.size) (h : SortedUntil arr i)
    : SortedUntil (insertSorted arr ⟨i, isLt⟩) (i + 1) := by
  induction i generalizing arr with
  | zero => apply singleton_sorted
  | succ n ih =>
    simp only [insertSorted]
    split
      -- We're done - the element is in place
    case inl hLe => exact insertSorted_sorted_no_swap (n + 1) arr isLt hLe h
    case inr hLe =>
      have next := ih (arr.swap ⟨n , by omega⟩ ⟨n + 1, by omega⟩) (by simp; omega) (insertSorted_swap_end n _ (by omega) (by apply prev_sorted; assumption))
      intro i ⟨hi, hi'⟩
      by_cases eq : i = n + 1
      -- The new one
      . right
        subst eq
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]

      -- An old one
      . apply next
        . constructor
          . omega
          . assumption



end
end Pairwise

namespace Less
def Sorted [LE α] (arr : Array α) : Prop :=
  ∀ i, (h : i < arr.size) → ∀ j, (h' : j < i) → arr[j]'(by omega) ≤ arr[i]

def SortedUntil [LE α] (arr : Array α) (stop : Nat) : Prop :=
  ∀ i, (h : i < stop ∧ i < arr.size) → ∀ j, (h' : j < i) → arr[j]'(by omega) ≤ arr[i]'(by omega)

section

variable [inst : LE α]

theorem sorted_until_all (arr : Array α) : SortedUntil arr arr.size ↔ Sorted arr := by
  unfold Sorted
  unfold SortedUntil
  constructor
  . intro h i hi j hj
    apply h
    constructor <;> assumption
    assumption
  . intro h i hi j hj
    apply h
    assumption

theorem empty_sorted (arr : Array α) : SortedUntil arr 0 := by
  unfold SortedUntil
  intro i h
  cases h
  contradiction

theorem singleton_sorted (arr : Array α) : SortedUntil arr 1 := by
  unfold SortedUntil
  intro i h
  cases h
  have : i = 0 := by
    cases ‹i < 1›
    . rfl
    . contradiction
  subst this
  intros
  contradiction

def insertSorted [DecidableRel inst.le] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i'+1, isLt⟩ =>
    have : i' < arr.size := by omega
    if arr[i'] ≤ arr[i] then
      arr
    else
      insertSorted (arr.swap ⟨i', by assumption⟩ i) ⟨i', by simp [*] ⟩

theorem insertSorted_sorted [DecidableRel inst.le] (i : Nat) (arr : Array α) : (isLt : i < arr.size) → SortedUntil arr i → SortedUntil (insertSorted arr ⟨i, isLt⟩) (i + 1) := by
  induction i generalizing arr with
  | zero => intros; apply singleton_sorted
  | succ n ih =>
    intros isLt hSorted
    simp only [insertSorted]
    split
    . intro i hi
      by_cases atEnd : i = n + 1
      . subst atEnd
        intr


end
