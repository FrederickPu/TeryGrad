import Init.Data.Vector.Basic
#check Array

-- n nested homogenous Array
inductive NArray (α : Type u) : Nat → Type u where
| mk₁ : Array α → NArray α 0
| mk₂ {n : Nat} : Array (NArray α n) → NArray α (n + 1)
-- (kernel) invalid nested inductive datatype 'Array', nested inductive datatypes parameters cannot contain local variables.
