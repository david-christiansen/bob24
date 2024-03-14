import Lean

namespace Bob.List

def filter (p : α → Prop) [DecidablePred p] (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => if p x then x :: filter p xs' else filter p xs'

def filter_length (p : α → Prop) [DecidablePred p] : (filter p xs).length ≤ xs.length := by sorry

inductive All (p : α → Prop) : List α → Prop where

theorem filter_all (p : α → Prop) [DecidablePred p]
    : All p (filter p xs) := by sorry

theorem filter_elem (p : α → Prop) [DecidablePred p] : x ∈ xs → p x → x ∈ filter p xs := by sorry

inductive Sublist : List α → List α → Prop where

theorem filter_sublist [DecidablePred p] : Sublist (filter p xs) xs := by sorry
