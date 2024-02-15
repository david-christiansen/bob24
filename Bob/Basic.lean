import Std

def hello := "world"

class DecidableLT (α : Type u) extends LT α where
  decLT : (x y : α) → Decidable (LT.lt x y)

instance [DecidableLT α] {x y : α} : Decidable (x < y) := DecidableLT.decLT _ _

instance [inst : LT α] [DecidableRel (@LT.lt α inst)] : DecidableLT α where
  decLT := inferInstance

def insertionSort [DecidableLT α] (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs => insert x (insertionSort xs)
where
  insert (y : α) : List α → List α
    | [] => [y]
    | z::zs => if y < z then y :: z :: zs else z :: insert y zs

#eval insertionSort [1,2,3]
#eval insertionSort [3,2,1]

macro "fin!" n:term : term => `(⟨$n, by omega⟩)

def insertionSortArr [DecidableLT α] (i : Nat) (arr : Array α) : Array α :=
  match i with
  | 0 => arr
  | i' + 1 => insertionSortArr i' (insert arr i')
where
  insert (arr : Array α) (i : Nat) : Array α :=
    if h : i + 1 < arr.size then
      have : i < arr.size := by omega
      if arr[i] < arr[i+1] then arr
      else insert (arr.swap (fin! i) ⟨i+1, h⟩) (i + 1)
    else arr
termination_by
  insert arr i => arr.size - i
decreasing_by
  simp_wf
  omega

example := Std.Range

macro_rules
  | `(tactic|get_elem_tactic_trivial) => `(omega)

def blah [Inhabited α] [DecidableLT α] (arr : Array α) : Array α := Id.run do
  let n := arr.size
  let mut arr : { xs : Array α // xs.size = n } := ⟨arr, rfl⟩
  for h : i in [0:n] do
    for h' : j in [0:i] do
      let j := i - j
      if arr.val[j]! < arr.val[j-1]! then
        arr := Subtype.mk (arr.val.swap ⟨j-1, by
          simp [Membership.mem] at h h';
          simp [j];
          cases ‹{xs // Array.size xs = n}›

        ⟩ ⟨j, _⟩) <| by
          simp; rename_i arr'; cases arr'; simp [*]
      else break
  pure arr

def ins [DecidableLT α] (arr : Array α) : Fin arr.size → Array α
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, h⟩ =>
    have : i' < arr.size := by omega
    if arr[i'+1] < arr[i'] then
      let arr' := arr.swap (fin! (i'+1)) (fin! i')
      have : arr.size = arr'.size := by simp
      ins arr' (fin! i')
    else arr

@[simp]
theorem insert_size [DecidableLT α] {arr : Array α} {i : Fin arr.size} : (ins arr i).size = arr.size := by
  cases i with | _ i h =>
  induction i generalizing arr
  . simp [ins]
  case succ i' ih =>
    simp [ins, ih]
    split
    . rw [ih]
      simp
    . rfl

def insertionSortArr' [DecidableLT α] (i : Nat) (arr : Array α) : Array α :=
  if h : i < arr.size then
    insertionSortArr' (i + 1) (ins arr ⟨i, h⟩)
  else arr
termination_by insertionSortArr' i arr => arr.size - i
decreasing_by
  simp_wf
  omega

namespace alsdkfjsladkfj
def insertSorted! [Inhabited α] [Ord α] (arr : Array α) (i : Nat) : Array α :=
  match i with
  | 0 => arr
  | i' + 1 =>
    match Ord.compare arr[i']! arr[i]! with
    | .lt | .eq => arr
    | .gt =>
      insertSorted!
        (arr.swap! i' i)
        i'

def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by omega
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted
        (arr.swap ⟨i', by assumption⟩ i)
        ⟨i', by simp [*]⟩

theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted, dbgTraceIfShared]
    split <;> simp [*]

partial def insertionSortLoop! [Inhabited α] [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if i < arr.size then
    insertionSortLoop! (insertSorted! arr i) (i + 1)
  else
    arr

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
      simp [Nat.sub_succ_lt_self, *]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by insertionSortLoop arr i => arr.size - i

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0


------------------


def rev (xs : List α) : List α :=
  match xs with
  | [] => []
  | y :: ys => rev ys ++ [y]

def rev'' (acc : List α) : List α → List α
  | [] => acc
  | y :: ys => rev'' (y :: acc) ys

def rev' (xs : List α) := rev'' [] xs

theorem rev_is_rev''_good : rev'' ys xs = rev xs ++ ys := by
  match xs with
  | [] => simp [rev, rev'']
  | z :: zs =>
    rw [rev'']
    rw [rev]
    rw [rev_is_rev''_good]
    simp only [List.singleton_append, List.append_assoc]

theorem rev_is_rev'' : rev xs = rev'' [] xs := by
  unfold rev
  unfold rev''
  match xs with
  | [] => simp
  | y :: ys => sorry

theorem rev_is_rev' : rev xs = rev' xs := by
  unfold rev'
  rw [rev_is_rev''_good]
  simp

def revArr! (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size / 2 then
    revArr! (arr.swap! i (arr.size - (i + 1))) (i + 1)
  else
    arr
termination_by
  revArr! arr i => arr.size - i
decreasing_by
  simp_wf
  rw [Array.size_swap!] <;> omega

#eval revArr! (.range 10) 0

def revArr (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size / 2 then
    revArr (arr.swap ⟨i, by omega⟩ ⟨arr.size - (i + 1), by omega⟩) (i + 1)
  else
    arr
termination_by
  revArr arr i => arr.size - i
decreasing_by
  simp_wf
  omega

-- Partiality does not infect callers!

def revImp (arr : Array α) : Array α := Id.run do
  let mut i := 0
  let mut arr := arr
  while h : i < arr.size / 2 do
    arr := arr.swap ⟨i, by omega⟩ ⟨arr.size - (i + 1), by omega⟩
    i := i + 1
  arr

#eval revImp (.range 5)

theorem foo : revImp arr = revArr arr 0 := by
  simp [revImp]
