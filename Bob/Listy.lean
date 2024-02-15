import Std
import Lean

namespace Lists
inductive All (p : α → Prop) : List α → Prop where
  | nil : All p []
  | cons : p x → All p xs → All p (x :: xs)

def filter (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | x :: xs => if p x then x :: filter p xs else filter p xs

def filter_length (p : α → Prop) [DecidablePred p] : (filter p xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    simp [filter]
    split
    . simp; omega
    . omega

theorem filter_all (p : α → Prop) [DecidablePred p] : All p (filter p xs) := by
  induction xs with
  | nil => constructor
  | cons x xs ih =>
    simp only [filter]
    split
    . constructor
      . assumption
      . assumption
    . assumption

theorem filter_elem (p : α → Prop) [DecidablePred p] : x ∈ xs → p x → x ∈ filter p xs := by
  intro hMem
  induction hMem with
  | head as =>
    intro hx
    simp [filter]
    split <;> try trivial
    constructor
  | tail h _ ih =>
    intro hx
    simp [filter]
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
    simp [filter]
    split
    . apply Sublist.cons; exact ih
    . apply Sublist.skip; exact ih
end Lists

namespace Arrays

def All (p : α → Prop) (arr : Array α) : Prop :=
  ∀ i, (lt : i < arr.size) → p arr[i]

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
theorem all_empty (p : α → Prop) : All p #[] := fun _ lt =>
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
      simp at isLt
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

end Arrays

open Lean (Json FromJson ToJson)

inductive Context where
  | object
  | array
  | val

inductive Query : Context → Type where
  | any : Query ctxt
  | none : Query ctxt
  | is (obj : Json) : Query .val
  | string : Query .val
  | obj : Query .object → Query .val
  | key : String → Query .val → Query .object
  | array : Query .array → Query .val
  | at : Nat → Query .val → Query .array
  | length : Nat → Query .array
  | and : Query ctxt → Query ctxt → Query ctxt
  | or : Query ctxt → Query ctxt → Query ctxt

abbrev Context.Subject : Context → Type
  | .val => Json
  | .array => Array Json
  | .object => Lean.RBNode String (fun _ => Json)

def Query.matches (q : Query ctxt) (v : ctxt.Subject) : Bool :=
  match q, v with
  | .any, _ => true
  | .none, _ => false
  | .is v', v => v == v'
  | .string, .str _ => true
  | .string, _ => false
  | .obj q', .obj fields => q'.matches fields
  | .obj _, _ => false
  | .key k q', fields =>
    if let some v := fields.find compare k then q'.matches v else false
  | .array q', .arr elts => q'.matches elts
  | .array _, _ => false
  | .at n q', elts =>
    if let some v := elts[n]? then q'.matches v else false
  | .length n, elts => elts.size == n
  | .and q1 q2, v => q1.matches v && q2.matches v
  | .or q1 q2, v =>  q1.matches v || q2.matches v

partial def Query.parse {ctxt: Context} (input : Json) : Except String (Query ctxt) := do
  match ctxt, input with
  | _, "any" => pure .any
  | _, "none" => pure .none
  | .val, .arr #["is", o] => pure (.is o)
  | .val, "string" => pure .string
  | .val, .arr #["object", o] => obj <$> parse o
  | .object, .obj fields =>
    let mut q : Query .object := .any
    for ⟨k, v⟩ in fields.toArray do
      q := .and q (.key k (← parse v))
    pure q
  | .object, other => throw s!"expected object, got {other}"
  | .val, .arr #["array", a] => array <$> parse a
  | .array, v@(.obj fields) =>
    match fields.toArray with
    | #[⟨"length", n⟩] =>
      let n' : Nat ← FromJson.fromJson? n
      pure (.length n')
    | #[⟨"at", n⟩, ⟨"satisfies", q'⟩] =>
      pure (.at (← FromJson.fromJson? n) (← parse q'))
    | _ => throw s!"expected object with single key 'length' or keys 'at' and 'satisfies', got {v}"
  | ctxt, .arr more =>
    if h : more.size > 2 then
      match more[0]'(by omega) with
      | "and" =>
        let q1 ← parse (more[1]'(by omega))
        let q2 ← parse (more[2]'(by omega))
        let mut q := .and q1 q2
        for h : i in [3:more.size] do
          q := .and q (← parse more[i])
        pure q
      | "or" =>
        let q1 ← parse (more[1]'(by omega))
        let q2 ← parse (more[2]'(by omega))
        let mut q := .or q1 q2
        for h : i in [3:more.size] do
          q := .or q (← parse more[i])
        pure q
      | other => throw s!"Expected 'and' or 'or', got {other}"
    else
      throw s!"Expected at least two elements in {more}"
  | ctxt, other => throw s!"didn't understand {other}"


open Lean.Parsec in
def readJsons (input : String) : Except String (Array Json) := do
  match jsons input.mkIterator with
  | .success _ v => pure v
  | .error _ e => throw e
where
  jsons : Lean.Parsec (Array Json) := do
    ws
    let val ← many Json.Parser.anyCore
    eof
    pure val

partial def readStdin : IO String := do
  let stdin ← IO.getStdin
  let mut str := ""
  let mut l ← stdin.getLine
  while !l.isEmpty do
    str := str ++ l
    l ← stdin.getLine
  pure str

def filterMain : List String → IO UInt32
  | [q] => do
    let query ←
      match Json.parse q >>= Query.parse (ctxt := .val) with
      | .error e => IO.eprintln e; return 1
      | .ok q' => pure q'
    let input ← readStdin
    match readJsons input with
    | .error e => IO.eprintln e; return 3
    | .ok vals =>
      for v in Arrays.filter (query.matches · = true) vals do
        IO.println v
      return 0
  | _ => do
    IO.println "Usage: jsonfilter QUERY"
    return 2
