-------------------------
-- Programming in Lean --
-------------------------

/-

Lean is very much like other functional programming languages. It has
recursive definitions by pattern matching, user-defined datatypes,
type classes, and do-notation for programming with monads.

-/

/-

Prior to the tutorial, all code is replaced with "sorry". This instructs Lean to accept the code
with missing pieces.

-/

-- Here's a function that doubles a natural number.
def double (n : Nat) : Nat := sorry

-- Test it using `#eval`, which is a bit like an in-editor REPL
-- #eval double 5

-- `#check` is used to to check types
#check double

-- Arguments that come "after the colon" can be matched with top-level
-- patterns, reminiscent of Haskell's multiple equations.
def double' : Nat → Nat := sorry

-- These may both be used.
def multiply (k : Nat) : Nat → Nat := sorry

-- Just as with Haskell type variables, arguments can just be used, and they're treated as
-- parameters to the whole function. Here, α is the type argument, implicitly specified just by
-- using it.
def append : List α → List α → List α := sorry

-- Datatypes are defined with "inductive"
inductive Tree (α : Type) where

-- Putting a function inside a type's namespace allows dot-notation:
def Tree.toList : Tree α → List α := sorry

-- #eval (Tree.branch (Tree.branch Tree.leaf 1 Tree.leaf) 2 Tree.leaf).toList

/-

Lean also has full dependent types, so types can mention values and values in types can compute.
Following the "propositions as types" principle, a proposition (logical statement) is represented as
a type that classifies evidence of its truth. Dependent types allow propositions to include ordinary
values, and thus be useful!

A predicate is a proposition with a free variable that might hold (or not) for a given value

-/
inductive Even : Nat → Prop where

-- example : Even 6 := .isEven 3

inductive Repeats (x : α) : List α → Prop where

-- example : Repeats 3 [3,3,3] := .cons (.cons (.cons .nil))

/-
Lean types come in two flavors:
 * Types that contain data
 * Propositions

The difference is that the rules of Lean are set up such that any two proofs of the same proposition
are considered equivalent - we don't get to care which proof we have, so the result of a program had
better not depend on it. This frees us from caring as well, so we don't have to worry _why_ two
things are equal.

Functions that return types (including propositions) are just as good as any other function. For
instance, this function takes two predicates over some type α and builds a new predicate that
asserts both:
-/

def Both (p q : α → Prop) : α → Prop := sorry

/-
For more details on this, please see _Theorem Proving in Lean 4_ and _Functional Programming in
Lean_.
-/
