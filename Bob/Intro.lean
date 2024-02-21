-------------------------
-- Programming in Lean --
-------------------------

/-

Lean is very much like other functional programming languages. It has
recursive definitions by pattern matching, user-defined datatypes,
type classes, and do-notation for programming with monads.

-/

-- Here's a function that doubles a natural number.
def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => double n' + 2

-- Test it using `#eval`, which is a bit like an in-editor REPL
#eval double 5

-- Other commands include `#check` to check types and `#print` to see the internal representation of
-- a definition
#check double
#print double

-- Arguments that come "after the colon" can be matched with top-level
-- patterns, reminiscent of Haskell's multiple equations.
def double' : Nat → Nat
  | 0 => 0
  | n + 1 => double' n + 2

-- These may both be used.
def multiply (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => multiply n k + n

-- Just as with Haskell type variables, arguments can just be used,
-- and they're treated as parameters to the whole function. Here, α is
-- the type argument, implicitly specified just by using it.
def append : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

-- Datatypes are defined with "inductive"
inductive Tree (α : Type) where
  | leaf : Tree α
  | branch : Tree α → α → Tree α → Tree α

-- Putting a function inside a type's namespace allows dot-notation:
def Tree.toList : Tree α → List α
  | leaf => []
  | branch l x r => l.toList ++ [x] ++ r.toList

-- Lean also has full dependent types, so types can mention values and
-- values in types can compute. Following the "propositions as types"
-- principle, a proposition (logical statement) is represented as a
-- type that classifies evidence of its truth. Dependent types allow
-- propositions to include ordinary values, and thus be useful!

-- This datatype is a proposition that takes a list as an argument. We
-- can only provide something with type `NonemptyList xs` when `xs` is
-- a `::`.
inductive NonemptyList : List α → Prop where
  | cons : NonemptyList (x :: xs) -- here x and xs are implicitly arguments

example : NonemptyList [1,2,3] := NonemptyList.cons


-- Lean types come in two flavors:
-- * Types that contain data
-- * Propositions
--
-- The difference is that the rules of Lean are set up such that any
-- two proofs of the same proposition are considered equivalent - we
-- don't get to care which proof we have, so the result of a program
-- had better not depend on it. This frees us from caring as well, so
-- we don't have to worry _why_ two things are equal.

-- Functions that return types (including propositions) are just as
-- good as any other function. For instance, this function takes two
-- predicates over some type α and builds a new predicate that asserts
-- both:

def Both (p q : α → Prop) : α → Prop := fun x => p x ∧ q x

-- For more details on this, please see _Theorem Proving in Lean 4_
-- and _Functional Programming in Lean_.
