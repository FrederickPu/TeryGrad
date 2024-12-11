#check Array

-- n nested homogenous Array
inductive NArray (α : Type u) : Nat → Type u where
| nil (n : Nat) : NArray α n
| cons₁ (a : α) (l : NArray α 1) : NArray α 1
| cons₂ {n : Nat} (a : NArray α n) (l : NArray α (n+1)) : NArray α (n + 1)

structure Path (shape : List Nat) :=
    path : List Nat
    lenLt : path.length < shape.length
    inBounds : ∀ i : Fin path.length, path.get i < shape.get ⟨i.val, Nat.lt_trans i.isLt lenLt⟩

def NArray.length {α : Type u} {n : Nat} : (array : NArray α n) → Nat
| nil n => 0
| cons₁ _ l => l.length.succ
| cons₂ _ l => l.length.succ

def NArray.get {α : Type u} {n : Nat} : (array : NArray α n) → (i : Fin array.length) → NArray α (n - 1)
| cons₁ _ _, _ => nil 0
| cons₂ a _,  ⟨0, _⟩ => a
| cons₂ _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩

def NArray.get? {α : Type u} {n : Nat} : (array : NArray α n) → Nat → Option (NArray α (n - 1))
| cons₁ _ _,  _ => some (nil 0)
| cons₂ a _, 0 => some a
| cons₂ _ as, i+1 => get? as i
| _, _ => none

def NArray.at {α : Type u} {n : Nat} (array : NArray α n) : (path : List Nat) → Option (NArray α (n - path.length))
| [] => some array
| a::l => match array.get? a with
          | some x => by {
            have : (n - (a :: l).length) = (n - 1) - l.length := by
                simp [Nat.Simproc.sub_add_eq_comm n l.length 1]
            rw [this]
            exact (x.at l)
          }
          | none => none
/-
    NArray where at each depth the elements have the same length
    [[1, 2], [2, 3]] is a Tensor but [[1, 2], [3]] is not
    same np.ndarray
-/
structure Tensor (α : Type u) (n : Nat) (shape : List Nat) : Type u :=
    (toNArray : NArray α n)
    (elementsUniform :
     ∀ path₁ path₂ : Path shape,
      path₁.path.length = path₂.path.length →
        (toNArray.at path₁.path) ≠ none ∧
        (toNArray.at path₁.path).map NArray.length = (toNArray.at path₂.path).map NArray.length)
-- (kernel) invalid nested inductive datatype 'Array', nested inductive datatypes parameters cannot contain local variables.
