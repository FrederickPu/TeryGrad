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

namespace Ops

-- Helper functiions for Ops

def value (self : Ops) : Int := sorry
-- https://en.wikipedia.org/wiki/Identity_element
-- def identity_element(op:Ops, dt:DType) -> ConstType: return dtypes.as_const({Ops.ADD:0, Ops.MUL:1, Ops.MAX:dtypes.min(dt)}[op], dt)

-- def can_pad(u:UOp, edges:Dict[UOp, UOp], visisted:Set[UOp]) -> bool:
--   if u.op in GroupOp.UnsafePad: return False
--   if (len(u.src) == 2 and u.src[0] in edges) or u in visisted: return True
--   visisted.add(u)
--   return all(can_pad(x.base, edges, visisted) for x in u.src)

-- # With True as the default, this matches the old symbolic behavior
-- def resolve(x, default:bool=True):
--   if not isinstance(x, UOp): return bool(x)
--   assert x.dtype is dtypes.bool, "UOp in resolve must be bool"
--   # NOTE: generating the text for the exception is expensive, so we do this
--   return bool(sx.vmin) if (sx:=x.simplify()).vmin == sx.vmax else default

-- # smax/smin are replacements for max/min that preserve symbolic
-- def _suop(lst, uop_fxn, python_fxn):
--   uops, nums = partition(lst, lambda x: isinstance(x, UOp))
--   return ssimplify(functools.reduce(uop_fxn, uops + ([python_fxn(nums)] if nums else [])))
-- def smax(*lst): return _suop(argfix(*lst), UOp.maximum, max)
-- def smin(*lst): return _suop(argfix(*lst), UOp.minimum, min)

-- def ssimplify(uop): return uop.ssimplify() if isinstance(uop, UOp) else uop
-- def sym_infer(uop: Union[UOp, int], var_vals: Dict[UOp, int]) -> int: return uop.sym_infer(var_vals) if isinstance(uop, UOp) else uop

-- # used for UOp and UPat
-- def pretty_print(x:Any, rep:Callable, srcfn=lambda x: x.src, cache=None, d=0)->str:
--   def dfs(x:Any, cache:dict):
--     for s in srcfn(x) or []:
--       cache.setdefault(s, [len(cache), 0, False])[1] += 1
--       if cache[s][1] == 1: dfs(s, cache)
--   if cache is None: dfs(x, cache:={})
--   if (cx:=cache.setdefault(x, [0,0,False]))[2]: return f"{' '*d} x{cx[0]}"
--   cx[2], srcs = True, ('None' if srcfn(x) is None else ''.join(f'\n{pretty_print(s, rep, srcfn, cache, d+2)},' for s in srcfn(x)))
--   return f"{' '*d}{f'x{cx[0]}:=' * (cx[1]>1)}{rep(x)}" % srcs

-- class UOpMetaClass(type):
--   ucache:Dict[Tuple, weakref.ReferenceType[UOp]] = {}
--   def __call__(cls, op:Ops, dtype:DType=dtypes.void, src:Tuple[UOp,...]=tuple(), arg:Any=None):
--     if (wret:=UOpMetaClass.ucache.get(key:=(op, dtype, src, arg), None)) is not None and (ret:=wret()) is not None: return ret
--     UOpMetaClass.ucache[key] = weakref.ref(created:=super().__call__(*key))
--     return created

end Ops

inductive MultiLazyBuffer
inductive Tensor

mutual
inductive View
| mk
  (shape : List (Int ⊕ UOp))
  (strides : List (Int ⊕ UOp))
  (offset : (Int ⊕ UOp))
  (mask : Option (List ((Int ⊕ UOp) × (Int ⊕ UOp))))
  (contiguous : Bool)

inductive ShapeTracker
| mk (views : List View)

-- like a variable
inductive UOp
| mk
  (op : Ops)
  (dtype : DType)
  (src : List UOp)
  (arg : Option ((ConstType ⊕ UOp ⊕ List ConstType) ⊕ ShapeTracker))
end

namespace View
variable (x : View)
def shape : View → List (Int ⊕ UOp) :=
 fun ⟨a, b, c, d, e⟩ => a
def strides : View → List (Int ⊕ UOp) :=
 fun ⟨a, b, c, d, e⟩ => b
def offset : View → Int ⊕ UOp :=
 fun ⟨a, b, c, d, e⟩ => c
def mask : View → Option (List ((Int ⊕ UOp) × (Int ⊕ UOp))) :=
 fun ⟨a, b, c, d, e⟩ => d
def contiguous : View → Bool :=
 fun ⟨a, b, c, d, e⟩ => e
end View

namespace UOp
variable (x : UOp)
def op :=
  match x with
  | mk op _ _ _ => op
def dtype :=
  match x with
  | mk _ dtype _ _ => dtype
def src :=
  match x with
  | mk _ _ src _ => src
def arg :=
  match x with
  | mk _ _ _ arg => arg

end UOp

structure UPat :=
  uop : UOp
  name : String

namespace UPat
variable (x : UPat)
def op := x.uop.op
def dtype := x.uop.dtype
def src := x.uop.src
def arg := x.uop.arg
end UPat

def ConstLike := ConstType ⊕ UOp ⊕ List ConstType
instance : Coe Int ConstLike := ⟨fun x => Sum.inl (x:ConstType)⟩

class SimpleMathTrait (α : Type u) :=
  alu : α → Ops → List α → α
  const_like : α → ConstLike → α
  dtype : α → Option DType

class MathTrait (α : Type u) extends SimpleMathTrait α :=

abbrev Variable := UOp
abbrev SInt := Int ⊕ UOp
