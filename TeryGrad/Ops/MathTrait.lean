import TeryGrad.Ops.basic
import TeryGrad.Ops.UOp
import TeryGrad.FromPython

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

instance : Neg ConstLike := ⟨neg'⟩
instance : Neg (ConstLike ⊕ α) := ⟨
  fun x => match x with
  | Sum.inl x₁ => Sum.inl (-x₁)
  | Sum.inr x₂ => Sum.inr (-x₂)
⟩


def bitwise_and (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.AND x reverse
def bitwise_or (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.OR x reverse
def xor (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.XOR x reverse
def idiv (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := _binop self Ops.IDIV x reverse
def sub (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α := if reverse then alu (ufix self x) Ops.ADD [-self] else alu self Ops.ADD [ufix self (-x)]
def div (self : α) (x : ConstLike ⊕ α) (reverse : Bool := False) : α :=
  if reverse then (ufix self x) * (alu self Ops.RECIP []) else self * (alu (ufix self x) Ops.RECIP [])

instance : FDiv α := ⟨fun x y => idiv x (Sum.inr y)⟩
instance : Div α := ⟨fun x y => div x (Sum.inr y)⟩
instance : AndOp α := ⟨fun x y => bitwise_and x (Sum.inr y)⟩
instance : OrOp α := ⟨fun x y => bitwise_or x (Sum.inr y)⟩
instance : Xor α := ⟨fun x y => xor x (Sum.inr y)⟩
-- idk what to do about the reverse operations (__rxor__, __ror__)

#check 1 / 2
instance [Coe α Bool] : BEq α := ⟨fun x y => (eq x (Sum.inr y) : α)⟩
instance [Coe α Bool] : LT α := ⟨fun x y => alu x Ops.CMPLT [ufix x (Sum.inr y)]⟩
-- instance [Coe α Bool] : LE α := ⟨fun x y => ¬ (y < x)⟩

end SimpleMathTrait

namespace MathTrait

-- # TODO: move to Tensor when new backward is done
-- def lshift(self, x, reverse=False): return self._binop(Ops.SHL, x, reverse)
-- def rshift(self, x, reverse=False): return self._binop(Ops.SHR, x, reverse)
-- def __lshift__(self, x): return self.lshift(x)
-- def __rshift__(self, x): return self.rshift(x)
-- def __rlshift__(self, x): return self.lshift(x, True)
-- def __rrshift__(self, x): return self.rshift(x, True
-- # not in Tensor
-- def __mod__(self, x): return self.alu(Ops.MOD, self.ufix(x))
-- def __rmod__(self, x): return self.ufix(x).alu(Ops.MOD, self
-- def maximum(self, x): return self.alu(Ops.MAX, self.ufix(x))
-- def minimum(self, x): return -(-self).maximum(-x)
-- def where(self, x, y): return self.alu(Ops.WHERE, x, x.ufix(y))
-- def threefry(self, seed): return self.alu(Ops.THREEFRY, seed)
-- def reciprocal(self): return self.alu(Ops.RECIP)
-- def sqrt(self): return self.alu(Ops.SQRT)
-- def sin(self): return self.alu(Ops.SIN)
-- def log2(self): return self.alu(Ops.LOG2)
-- def exp2(self): return self.alu(Ops.EXP2)
end MathTrait
