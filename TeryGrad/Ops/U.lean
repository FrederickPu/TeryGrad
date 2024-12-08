import TeryGrad.Ops.basic
import Std.Data.HashMap.Basic
import TeryGrad.FromPython

-- method definitions for UOp and UPat

namespace UOp
def UOp.default (op : Ops) := UOp.mk op DType.void [] none

def alu : UOp → Ops → List Uop → UOp := sorry
-- out_dtype = (self, *src)[-1].dtype
-- if arg in {Ops.CMPLT, Ops.CMPNE}: out_dtype = dtypes.bool.vec(out_dtype.count) if out_dtype.count > 1 else dtypes.bool
-- return UOp(arg, out_dtype, (self,)+src)

def const_like : UOp → ConstLike → UOp := sorry
instance : MathTrait UOp := {
  alu := alu, const_like := const_like,
  dtype := fun x =>
    match x with
    | UOp.mk _ dtype _ _ => dtype
}

-- instance : ToString UOp :=
-- ⟨fun self => toString f!"{self.op}, {self.dtype}, {self.src}, {self.arg}"⟩
-- no need for replace cause we can just do { s with field1 := val1, field2 := val2 }
/-!
  For example:
  structure Point :=
    x : Nat
    y : Nat

  #check { (⟨1, 2⟩ : Point) with x := 3}
-/
def key (self : UOp) : ByteArray := sorry
def const : DType → Bool → UOp := sorry

/- Called tupilize in tinygrad
-/
inductive ListTree (α : Type u)
| mk (root : α) (children : List (ListTree α))

instance {α : Type u} [Inhabited α] : Inhabited (ListTree α) := ⟨ListTree.mk Inhabited.default []⟩

partial def listlize (self:UOp) : ListTree (Int × Option (ConstLike ⊕ ShapeTracker) × Option DType) :=
  ListTree.mk (self.op.value, self.arg, self.dtype) (self.src.map listlize)

instance : BEq Ops := sorry
def has_st (self : UOp) : Bool := [Ops.DEFINE_LOCAL, Ops.DEFINE_GLOBAL, Ops.BUFFER, Ops.CONST, Ops.DEFINE_VAR].contains self.op

instance : Coe UOp Bool := sorry

#check Std.HashMap
#check String.hash
#check ByteArray
end UOp
