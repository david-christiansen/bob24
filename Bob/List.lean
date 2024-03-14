import Lean

namespace Bob.List

def filter (p : α → Prop) [DecidablePred p] (xs : List α) : List α := xs
