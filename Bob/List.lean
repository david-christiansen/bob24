import Lean

namespace Bob.List

def filter (p : α → Prop) [DecidablePred p] (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => if p x then x :: filter p xs' else filter p xs'

def filter_length (p : α → Prop) [DecidablePred p] : (filter p xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    simp only [filter]
    split
    . simp only [List.length];
      exact Nat.add_le_add_right ih 1
    . exact Nat.le_succ_of_le ih

inductive All (p : α → Prop) : List α → Prop where
  | /-- `p` certainly holds for all zero entries of the empty list -/
    nil : All p []
  | /-- If `p` holds for the head and holds for all entries in the tail,
    then it holds for the combined list -/
    cons : p x → All p xs → All p (x :: xs)

theorem filter_all (p : α → Prop) [DecidablePred p]
    : All p (filter p xs) := by
  induction xs with
  | nil => constructor
  | cons x xs ih =>
    unfold filter
    split
    next h =>
      apply All.cons
      . exact h
      . exact ih
    next =>
      assumption

theorem filter_elem (p : α → Prop) [DecidablePred p] : x ∈ xs → p x → x ∈ filter p xs := by
  intro hMem
  induction hMem with
  | head as =>
    intro hx
    unfold filter
    split <;> try trivial
    constructor
  | tail h _ ih =>
    intro hx
    unfold filter
    split
    . constructor; apply ih; assumption
    . apply ih; assumption

inductive Sublist : List α → List α → Prop where
  | nil : Sublist [] ys
  | skip : Sublist xs ys → Sublist xs (y :: ys)
  | cons : Sublist xs ys → Sublist (x :: xs) (x :: ys)

theorem filter_sublist [DecidablePred p] : Sublist (filter p xs) xs := by
  induction xs with
  | nil =>
    constructor
  | cons head tail ih =>
    unfold filter
    split
    . apply Sublist.cons; exact ih
    . apply Sublist.skip; exact ih
