import Std

namespace Bob.Array

def All (p : α → Prop) (arr : Array α) : Prop :=
  ∀ i, (lt : i < arr.size) → p arr[i]

-- This implementation of `filter` shows a few interesting aspects of Lean:

-- * Lean's `do`-notation contains syntax for mutable variables and
--   iteration. These are translated behind the scenes to appropriate
--   monad transformers.
--
-- * `Array.push` will mutate the array in place if the array value's
--   reference count is exactly 1, so this code's seeming use of mutation
--   becomes real mutation, with accidental aliasing leading to extra copying
--   instead of scary bugs
def filter1 (p : α → Prop) [DecidablePred p] (arr : Array α) : Array α := Id.run do
  let mut out := #[]
  for x in arr do
    if p x then out := out.push x
  pure out

-- This version of `filter` is easier to prove things about. `do`
-- notation is nice, but the desugared programs are more difficult to
-- use in verification than hand-written loops/tail-recursive
-- functions.
def filter (p : α → Prop) [DecidablePred p] (arr : Array α) : Array α :=
  let rec go (i : Nat) (acc : Array α) : Array α :=
    if h : i < arr.size then
      if p arr[i] then
        go (i + 1) (acc.push arr[i])
      else
        go (i + 1) acc
    else acc
  termination_by arr.size - i
  go 0 #[]

@[simp]
theorem all_empty (p : α → Prop) : All p #[] := fun i lt =>
  -- nomatch is a compiler-checked assertion that a code path is
  -- unreachable. Here, `lt` has type i < 0, because #[].size = 0.
  -- The type i < 0 has no constructors, so this function can never be
  -- called with such a proof.
  nomatch lt

theorem push_all (p : α → Prop) : All p xs → p x → All p (xs.push x) := by
  intros
  have : (xs.push x)[xs.size] = x := by simp
  intro i isLt
  by_cases eq : i = xs.size
  . subst eq
    rw [this]
    assumption
  . have : i < xs.size := by
      simp only [Array.size_push] at isLt
      omega
    rename All p xs => hAll
    rw [Array.get_push]
    split <;> try contradiction
    apply hAll

theorem filter_go_all (p : α → Prop) [DecidablePred p] : All p acc → All p (filter.go p xs i acc) := by
  intro h
  unfold filter.go
  split
  . split
    . apply filter_go_all p (push_all _ _ _) (i := i + 1) <;> assumption
    . apply filter_go_all p h (i := i + 1)
  . assumption
termination_by xs.size - i

theorem filter_all (p : α → Prop) [DecidablePred p] : All p (filter p xs) := by
  simp [filter, filter_go_all]
