inductive DType
| void

inductive ConstType

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

mutual
  inductive SimpleMathTrait
  | ofMathTrait : MathTrait → SimpleMathTrait
  | ofTensor : Tensor → SimpleMathTrait
  inductive Tensor
  inductive MathTrait
  | ofUOp : UOp → MathTrait
  | ofMultiLazyBuffer : MultiLazyBuffer → MathTrait
  | ofLazyBuffer : LazyBuffer → MathTrait
  inductive UOp
  | mk
    (op : Ops)
    (dtype : DType)
    (src : List UOp)
    (arg : Option String)
  inductive MultiLazyBuffer
  inductive LazyBuffer
end

def ConstLike := ConstType ⊕ UOp ⊕ List ConstType

namespace UOp
def alu : UOp → Ops → UOp := sorry
end UOp

namespace LazyBuffer
def alu : LazyBuffer → Ops → LazyBuffer := sorry
end LazyBuffer

namespace MultiLazyBuffer
def alu : MultiLazyBuffer → Ops → MultiLazyBuffer := sorry
end MultiLazyBuffer

namespace Tensor
def alu : Tensor → Ops → Tensor := sorry
end Tensor

namespace MathTrait
def alu : MathTrait → Ops → MathTrait
| ofUOp u, o => ofUOp (u.alu o)
| ofMultiLazyBuffer m, o => ofMultiLazyBuffer (m.alu o)
| ofLazyBuffer l, o => ofLazyBuffer (l.alu o)
end MathTrait

namespace SimpleMathTrait
def alu : SimpleMathTrait → Ops → SimpleMathTrait
| ofMathTrait m, o => ofMathTrait (m.alu o)
| ofTensor t, o => ofTensor (t.alu o)
end SimpleMathTrait
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
-- -- the below line seems to suggest that everything is either ConstLike or a MathTrait
-- -- def ufix(self, x): return self.const_like(x) if not isinstance(x, MathTrait) else x-- TODO :: show that UOp is a mathtrait
-- end MathTrait
