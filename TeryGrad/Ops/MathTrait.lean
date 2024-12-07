import TeryGrad.Ops.basic
import TeryGrad.Ops.UOp
import TeryGrad.FromPython

def ConstLike := ConstType ⊕ UOp ⊕ List ConstType

instance : Coe Int ConstLike := ⟨fun x => Sum.inl (x:ConstType)⟩

/--
  the below coecersion instance should be in utils or smth
-/
instance {α : Type u} {β : Type v} {γ : Type w} [Coe α β] : Coe α (β ⊕ γ) :=
  ⟨fun x => Sum.inl (Coe.coe x)⟩
instance {α : Type u} {β : Type v} {γ : Type w} [Coe α γ] : Coe α (β ⊕ γ) :=
  ⟨fun x => Sum.inr (Coe.coe x)⟩
instance {α : Type u} : Coe α α :=
  ⟨fun x => x⟩

instance {α : Type u} {β : Type v} : Coe α (α ⊕ β) := by infer_instance

namespace SimpleMathTrait
variable {α : Type u} [SimpleMathTrait α]

def ufix (self : α) : ConstLike ⊕ α → α
| Sum.inl x => const_like self x
| Sum.inr x => x

def _binop (self : α) (op : Ops) (x : ConstLike ⊕ α) (reverse : Bool) : α :=
  if reverse then alu (ufix self x) op [self] else alu self op [ufix self x]

def ne (self : α) (x : ConstLike ⊕ α) : α := alu self Ops.CMPNE [ufix self x]
def logical_not (self : α) : α := ne self (Sum.inl <| Sum.inl (Sum.inr <| Sum.inr true))
def eq (self : α) (x : ConstLike ⊕ α) : α := logical_not (ne self x)

def mul (self : α) (x : ConstLike ⊕ α) (reverse : Bool := false) : α := _binop self Ops.MUL x reverse
def add (self : α) (x : ConstLike ⊕ α) (reverse : Bool := false) : α := _binop self Ops.ADD x reverse

def neg (self : α) : α := match dtype self with
  | none => panic! s!"MathTraits __neg__ requires a dtype, "
  | some x => match (dtype self) with
    | some x => match x._scalar with
      | some x' => if x'.name == "bool" then logical_not self else mul self ((-1:Int) : ConstLike ⊕ α)
      | none => mul self ((-1:Int) : ConstLike ⊕ α)
    | none => mul self ((-1:Int) : ConstLike ⊕ α)

instance : Neg α := ⟨neg⟩

instance : SimpleMathTrait UOp := inferInstance
instance : Neg UOp := inferInstance

def neg' (x : ConstLike) : ConstLike :=
match x with
| Sum.inl x₁ => Sum.inl (-x₁)
| Sum.inr x' =>
  match x' with
  | Sum.inl x₂ => Sum.inr (Sum.inl (-x₂))
  | Sum.inr x₃ => Sum.inr (Sum.inr <| x₃.map (fun y => -y))

instance : Neg (ConstLike ⊕ α) := ⟨
  fun x => match x with
  | Sum.inl x₁ => Sum.inl (neg' x₁)
  | Sum.inr x₂ => Sum.inr (-x₂)
⟩

def bitwise_and (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.AND x reverse
def bitwise_or (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.OR x reverse
def xor (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.XOR x reverse
def idiv (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.IDIV x reverse
def sub (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := if reverse then alu (ufix self x) Ops.ADD [-self] else alu self Ops.ADD [ufix self (-x)]
def div (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α :=
  if reverse then mul (ufix self x) (alu self Ops.RECIP [] : α) else mul self (alu (ufix self x) Ops.RECIP [] : α)

instance : OrOp α := ⟨fun x y => bitwise_or x (Sum.inr y)⟩
instance : Xor α := ⟨fun x y => xor x (Sum.inr y)⟩

/- Right Heterogenous
-/
instance : HAdd α (ConstLike ⊕ α) α := ⟨fun x y => add x y⟩
instance : HSub α (ConstLike ⊕ α) α := ⟨fun x y => sub x y⟩
instance : HMul α (ConstLike ⊕ α) α := ⟨fun x y => mul x y⟩
instance : HDiv α (ConstLike ⊕ α) α := ⟨fun x y => div x y⟩
instance : HFDiv α (ConstLike ⊕ α) α := ⟨fun x y => idiv x y⟩
instance : HAnd α (ConstLike ⊕ α) α := ⟨fun x y => bitwise_and x y⟩
instance : HOr α (ConstLike ⊕ α) α := ⟨fun x y => bitwise_or x y⟩
instance : HXor α (ConstLike ⊕ α) α := ⟨fun x y => xor x y⟩

/- Homogenous
-/
instance : Add α := ⟨fun x y => add x y⟩
instance : Sub α := ⟨fun x y => sub x y⟩
instance : Mul α := ⟨fun x y => mul x y⟩
instance : Div α := ⟨fun x y => div x y⟩
instance : FDiv α := ⟨fun x y => idiv x y⟩
instance : AndOp α := ⟨fun x y => bitwise_and x y⟩
instance : OrOp α := ⟨fun x y => bitwise_or x y⟩
instance : Xor α := ⟨fun x y => xor x y⟩

/- Left Heterogenous
-/
instance : HAdd (ConstLike ⊕ α) α α := ⟨fun x y => add y x true⟩
instance : HSub (ConstLike ⊕ α) α α := ⟨fun x y => sub y x true⟩
instance : HMul (ConstLike ⊕ α) α α := ⟨fun x y => mul y x true⟩
instance : HDiv (ConstLike ⊕ α) α α := ⟨fun x y => div y x true⟩
instance : HFDiv (ConstLike ⊕ α) α α := ⟨fun x y => idiv y x true⟩
instance : HAnd (ConstLike ⊕ α) α α := ⟨fun x y => bitwise_and y x true⟩
instance : HOr (ConstLike ⊕ α) α α := ⟨fun x y => bitwise_or y x true⟩
instance : HXor (ConstLike ⊕ α) α α := ⟨fun x y => xor y x true⟩

#check 1 / 2
instance [Coe α Bool] : BEq α := ⟨fun x y => (eq x (Sum.inr y) : α)⟩
instance [Coe α Bool] : LT α := ⟨fun x y => alu x Ops.CMPLT [ufix x (Sum.inr y)]⟩
-- TODO :: make this less scuffed by having HLT and HLE
instance [Coe α Bool] : LE α := ⟨fun x y => (logical_not (alu x Ops.CMPLT [ufix x (Sum.inr y)]) : α)⟩

-- from MathTrait in the python implementation
-- # TODO: move to Tensor when new backward is done
def lshift (self : α) (x : ConstLike ⊕ α) (reverse : Bool := false) : α := _binop self Ops.SHL x reverse
def rshift (self : α) (x : ConstLike ⊕ α) (reverse : Bool := false) : α := _binop self Ops.SHR x reverse
instance : HShiftLeft α (ConstLike ⊕ α) α := ⟨lshift⟩
instance : HShiftRight α (ConstLike ⊕ α) α := ⟨rshift⟩

-- # not in Tensor
instance : HMod α (ConstLike ⊕ α) α :=
  ⟨fun self x => alu self Ops.MOD [ufix self x]⟩
instance : HMod (ConstLike ⊕ α) α α :=
  ⟨fun x self => alu (ufix self x) Ops.MOD [self]⟩

def maximum (self : α) (x : ConstLike ⊕ α) : α := alu self Ops.MOD [ufix self x]
def minimum (self : α) (x : ConstLike ⊕ α) : α := -(maximum (-self) (-x))
def where_ (self x : α) (y : ConstLike ⊕ α) : α := alu self Ops.WHERE [x, ufix x y]
def threefry (self : α) (seed : α) : α := alu self Ops.THREEFRY [seed]
def reciprocal (self : α) : α := alu self Ops.RECIP []
def sqrt (self : α) : α := alu self Ops.SQRT []
def sin (self : α) : α := alu self Ops.SIN []
def log2 (self : α) : α := alu self Ops.LOG2 []
def exp2 (self : α) : α := alu self Ops.EXP2 []

end SimpleMathTrait
