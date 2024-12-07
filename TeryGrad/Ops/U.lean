import TeryGrad.Ops.basic

-- method definitions for UOp and UPat

namespace UOp
def alu : UOp → Ops → List Uop → UOp := sorry
-- out_dtype = (self, *src)[-1].dtype
-- if arg in {Ops.CMPLT, Ops.CMPNE}: out_dtype = dtypes.bool.vec(out_dtype.count) if out_dtype.count > 1 else dtypes.bool
-- return UOp(arg, out_dtype, (self,)+src)

def const_like : UOp → ConstLike → UOp := sorry
instance : MathTrait UOp := {
  alu := alu, const_like := const_like,
  dtype := fun x =>
    match x with
    | mk _ dtype _ _ => dtype
}

def UOp.default (op : Ops) := UOp.mk op DType.void [] none
end UOp
