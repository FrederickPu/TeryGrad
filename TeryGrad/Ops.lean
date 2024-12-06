import TeryGrad.DType

inductive Ops
  -- uops that aren't rendered
  | SINK | CONTIGUOUS | PRELOAD
  -- MetaOps
  | COPY | EMPTY | BUFFER_VIEW
  -- blocks in linearizer
  | BLOCK | BLOCKSTART | BLOCKFORK | BLOCKEND
  -- misc ops
  | EXPAND | CONTRACT
  | VIEW | DEFINE_GLOBAL | BUFFER
  | DEFINE_VAR | DEFINE_LOCAL | DEFINE_ACC
  | VALID | SPECIAL | NOOP
  -- reduce
  | REDUCE_AXIS
  -- helper ops
  | GEP | VECTORIZE
  -- UnaryOps
  | CAST | BITCAST | EXP2 | LOG2 | SIN | SQRT | RECIP | NEG
  -- load/store before math
  | LOAD | STORE
  -- early INDEX
  | INDEX
  -- math ops
  | WMMA
  -- BinaryOps
  | ADD | MUL | IDIV | MAX | MOD | CMPLT | CMPNE | XOR
  | SHL | SHR | OR | AND | THREEFRY | SUB | FDIV
  -- TernaryOps
  | WHERE | MULACC
  -- assignment ops
  | ASSIGN | BIND
  -- control flow ops
  | BARRIER | RANGE | IF | ENDRANGE | ENDIF
  -- consts last!
  | VCONST | CONST

inductive MultiLazyBuffer
inductive LazyBuffer
inductive Tensor

inductive UOp
| mk
  (op : Ops)
  (dtype : DType)
  (src : List UOp)
  (arg : Option String)

def ConstLike := ConstType ⊕ UOp ⊕ List ConstType

instance : Coe Int ConstLike := ⟨fun x => Sum.inl (x:ConstType)⟩

class SimpleMathTrait (α : Type u) :=
  alu : α → Ops → List α → α
  const_like : α → ConstLike → α
  dtype : α → Option DType


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

end SimpleMathTrait

class MathTrait (α : Type u) extends SimpleMathTrait α :=

namespace UOp
def alu : UOp → Ops → List Uop → UOp := sorry
def const_like : UOp → ConstLike → UOp := sorry
instance : MathTrait UOp := {
  alu := alu, const_like := const_like
}

def UOp.default (op : Ops) := UOp.mk op DType.void [] none

end UOp

namespace LazyBuffer
def alu : LazyBuffer → Ops → List LazyBuffer → LazyBuffer := sorry
def const_like : LazyBuffer → ConstLike → LazyBuffer := sorry
instance : MathTrait LazyBuffer := {
  alu := alu, const_like := const_like
}
end LazyBuffer

namespace MultiLazyBuffer
def alu : MultiLazyBuffer → Ops → List MultiLazyBuffer → MultiLazyBuffer := sorry
def const_like : MultiLazyBuffer → ConstLike → MultiLazyBuffer := sorry
instance : MathTrait MultiLazyBuffer := {
  alu := alu, const_like := const_like
}
end MultiLazyBuffer

namespace Tensor
def alu : Tensor → Ops → List Tensor → Tensor := sorry
def const_like : Tensor → ConstLike → Tensor := sorry
instance : SimpleMathTrait Tensor := ⟨alu, const_like⟩
end Tensor

-- def UOp.default (op : Ops) := UOp.mk op DType.void [] none

-- -- only the data carrying part of UOp

-- def ConstLike := ConstType ⊕ UOp ⊕ List ConstType

-- -- we are going to assume George Hotz is smart and doesn't reimplement derived methods
-- class SimpleMathTrait (α : Type u) :=
--   alu : α → Ops → α
--   const_like : α → ConstLike → α

-- namespace SimpleMathTrait
-- -- TODO :: show that UOp is a simplemathtrait
-- end SimpleMathTrait

-- namespace MathTrait

-- variable {α : Type u} [SimpleMathTrait α]
-- -- the below line seems to suggest that x is either ConstLike or a MathTrait
-- -- def ufix(self, x): return self.const_like(x) if not isinstance(x, MathTrait) else x-- TODO :: show that UOp is a mathtrait
-- end MathTrait
