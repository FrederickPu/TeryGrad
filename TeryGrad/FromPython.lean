universe u v w u₁ u₂

class Iterable (α : Type u) (β : outParam (Type v)) :=
  (iter : α → α)       -- Initializes the iterator
  (next : α → Option (β × α)) -- Retrieves the next value and updates the iterator state

/--
  Map can have multiple implmentations. For example HashMap (Map (HasMap β γ) β γ) is an implementation.
  and HashMap using int256 instead of int64 would also work
-/
class Map (α : Type u) (β : Type v) (γ : outParam (Type w)) :=
  (keys : α → List β)
  (get : α → β → Option γ)
  (nodup (a : α) : (keys a).Nodup) -- there are no duplicates in the keys list
  (get_defined_iff (a : α) : ∀ k, k ∈ keys a ↔ get a k ≠ none) -- a[k] is defined if k ∈ a.keys()

/--
  Set can have multiple implmentations. For example HashSet (Set (HashSet β) β) is an implementation.
  and HashSet using int256 instead of int64 would also work
-/
class Set (α : Type u) (β : Type v) :=
  (elems : α → List β)
  (nodup (a : α) : (elems a).Nodup)

instance : Iterable (List β) β :=
{
  iter := id,  -- For lists, the "initial state" is the list itself
  next := fun xs => match xs with
    | []      => none          -- No more elements
    | (x::xs) => some (x, xs)  -- Return head and tail
}

/--
From batteries
Get the value out of a `ForInStep`.
This is usually done at the end of a `forIn` loop to scope the early exit to the loop body.
-/
@[inline] def ForInStep.run : ForInStep α → α
  | .done a
  | .yield a => a

namespace Iterable

partial instance instForIn {m : Type u₁ → Type u₂} {ρ : Type u} {α : outParam (Type v)} [Iterable ρ α] : ForIn m ρ α :=
{
  forIn := fun {β} [Monad m] x init f =>
     -- termination is not guaranteed since some iterators might never return a terminal state
    let rec aux (state : ρ) (acc : β) : m β :=
      match Iterable.next state with
      | none          => pure acc
      | some ⟨val, s⟩ => do
          let newAcc ← f val acc
          aux s (ForInStep.run newAcc)
    aux (Iterable.iter x) init
}

def reduce {α : Type u} {β : Type v} [Iterable α β] (op : β → β → β) (a : α) (b : β) := Id.run do
  let mut acc := b
  for x in a do
    acc := op acc x
  return acc

end Iterable


inductive NestedList (α : Type u)
| nil : NestedList α  -- []
| cons₁ : α → NestedList α → NestedList α  -- a l => [a, ...l]
| cons₂ : NestedList α → NestedList α → NestedList α -- l₁ l₂ → [l₁, ...l₂]

def aux {α : Type} [ToString α] : NestedList α → String
| NestedList.nil => ""
| NestedList.cons₁ a NestedList.nil => toString a
| NestedList.cons₁ a l => toString a ++ ", " ++ aux l
| NestedList.cons₂ a NestedList.nil => "[" ++ aux a ++ "]"
| NestedList.cons₂ a l => "[" ++ aux a  ++ "]" ++ ", " ++ aux l

instance  {α : Type} [ToString α] : ToString (NestedList α) :=
  ⟨fun x => "[" ++ aux x ++ "]"⟩

def exampleNestedList : NestedList Nat :=
  NestedList.cons₂ (NestedList.cons₁ 1 (NestedList.cons₁ 2 NestedList.nil)) NestedList.nil -- [[1, 2]]


syntax "N[" term,* "]" : term

macro_rules
  | `(N[]) => `(NestedList.nil)
  | `(N[N[$xs,*]]) => `(NestedList.cons₂ N[$xs,*] NestedList.nil)
  | `(N[N[$xs,*], $ys,*]) => `(NestedList.cons₂ N[$xs,*] N[$ys,*])
  | `(N[$x]) => `(NestedList.cons₁ $x NestedList.nil)
  | `(N[$x, $xs,*]) => `(NestedList.cons₁ $x N[$xs,*])

#eval N[N[1,2]]
-- N[N[1, 2]]
#eval N[1,N[2,3],4,N[N[5,6],7]]
-- N[1, N[2, 3], 4, N[N[5, 6], 7]]

-- TODO:: make it so you only need to use N once that is you can use
-- N[1, [1, 2]] instead of N[1, N[2, 3]]

/--
The notation typeclass for heterogeneous floor division.
This enables the notation `a ⌊/⌋ b : γ` where `a : α`, `b : β`.
-/
class HFDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hFDiv : α → β → γ

/--
The notation typeclass for floor division.
-/
class FDiv (α : Type u) where
  hFDiv : α → α → α

instance {α : Type u} [FDiv α] : HFDiv α α α :=
  ⟨fun a₁ a₂ => FDiv.hFDiv a₁ a₂⟩

macro_rules | `($x "⌊/⌋" $y)   => `(binop% HFDiv.hFDiv $x $y)
