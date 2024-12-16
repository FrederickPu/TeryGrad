import TeryGrad.FromPython

universe u v w

variable {T : Type u} {U : Type v} {β : Type w} [OfNat T 1] [Mul T] [BEq T]

-- NOTE: it returns int 1 if x is empty regardless of the type of x
def prod [Iterable β T] (x : β) : T := Iterable.reduce (· * ·) x 1
def dedup [Iterable β T] (x : β) : List T := Id.run do
  let mut acc := []
  for y in x do
    acc := List.cons y acc
  return acc
-- no argfix or argsort cause u cant have dynamic arguments in lean
def argfix : False := sorry
def argsort : False := sorry
-- note that lists are immutable in lean so no need to tuples
def all_same : (items: List T) → Bool
| a::b::l => a == b && all_same (b::l)
| _ => true
def allint : False := sorry
def colored : False := sorry
-- ... some other missing methods
def flatten [Iterable β T] (x : β) : List T := Id.run do
  let mut acc := []
  for y in x do
    acc := acc ++ [y]
  return acc
def fully_flatten : (x : NestedList T) → List T
| NestedList.nil => []
| NestedList.cons₁ a l => a :: (fully_flatten l)
| NestedList.cons₂ l₁ l₂ => (fully_flatten l₁) ++ (fully_flatten l₂)
-- from_import
-- strip_parens
def ceil_div (a b : Float) := (a / b).ceil

def unwrap {T : Type u} [Inhabited T] (x : Option T) : T :=
  match x with
  | some value => value
  | none       => panic! "unwrap called on none"
