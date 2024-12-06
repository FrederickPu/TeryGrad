import TeryGrad.Ops.basic
import TeryGrad.Ops.UOp

def ConstLike := ConstType ⊕ UOp ⊕ List ConstType

instance : Coe Int ConstLike := ⟨fun x => Sum.inl (x:ConstType)⟩

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
instance : Mul α := ⟨fun x y => mul x (Sum.inr y)⟩
instance : HMul α (ConstType ⊕ UOp ⊕ List ConstType) α := ⟨fun x y => mul x (Sum.inl y)⟩
instance : Add α := ⟨fun x y => add x (Sum.inr y)⟩
instance : HAdd α (ConstType ⊕ UOp ⊕ List ConstType) α := ⟨fun x y => add x (Sum.inl y)⟩

def neg (self : α) : α := match dtype self with
  | none => panic! s!"MathTraits __neg__ requires a dtype, "
  | some x => match (dtype self) with
    | some x => match x._scalar with
      | some x' => if x'.name == "bool" then logical_not self else (self * ((-1:Int) : ConstLike))
      | none => (self * ((-1:Int) : ConstLike))
    | none => (self * ((-1:Int) : ConstLike))

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


def bitwise_and (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.AND x reverse
def bitwise_or (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.OR x reverse
def xor (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.XOR x reverse
def idiv (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.IDIV x reverse
def sub (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := if reverse then alu (ufix self x) Ops.ADD [-self] else alu self Ops.ADD (ufix self (-x))

instance [Coe α Bool] : BEq α := ⟨fun x y => (eq x (Sum.inr y) : α)⟩

end SimpleMathTrait
