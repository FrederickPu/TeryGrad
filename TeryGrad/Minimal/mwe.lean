import Batteries.Logic

inductive DiffTree (α : Type u) (β : Type v) : List Nat → Type (max u v)
| mk
    (outShape : List Nat)
    (parents : Array (Σ shape, DiffTree α β shape))
    : DiffTree α β outShape


inductive DiffTree.valid {α : Type u} {β : Type v} : ∀ (shape : List Nat), DiffTree α β shape → Prop
| mk (outShape : List Nat) (parents : Array (Σ shape, DiffTree α β shape)) : (DiffTree.mk outShape parents).valid

example (shapeX : List Nat)
    (X : DiffTree α β shapeX)
    (shapeP : List Nat)
    (P : DiffTree α β shapeP)
    (H1 : shapeX = shapeP)
    (H2 : HEq P X)
    (hv : P.valid) : X.valid := by
  cases H1
  cases H2
  exact hv

/-
  α : Type u_1
β : Type u_2
shapeX : List Nat
X : DiffTree α β shapeX
shapeP : List Nat
P : DiffTree α β shapeP
H : shapeX = shapeP ∧ HEq P X
hv : DiffTree.valid shapeP P
temp : DiffTree α β shapeX := cast ⋯ P
this : temp = X
⊢ DiffTree.valid shapeX (cast ⋯ P)
-/
