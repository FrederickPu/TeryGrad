universe u v w u₁ u₂

class Iterable (α : Type u) (β : outParam (Type v)) :=
  (iter : α → α)       -- Initializes the iterator
  (next : α → Option (β × α)) -- Retrieves the next value and updates the iterator state

class Map (α : Type u) (β : Type v) (γ : outParam (Type w)) :=
  (keys : α → List β)
  (get : α → β → Option γ)
  (h₁ (a : α) : (keys a).Nodup) -- there are no duplicates in the keys list
  (h₂ (a : α) : ∀ k, k ∈ keys a ↔ get a k ≠ none) -- a[k] is defined if k ∈ a.keys()


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

-- TODO:: make a macro parser for it
