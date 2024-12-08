import TeryGrad.Shape.ShapeTracker
import TeryGrad.Ops.U

namespace UOp

def st (self : UOp) : Option ShapeTracker := Id.run do
    if self.op == Ops.VIEW then
      match self.arg with
      | some x => match x with
        | Sum.inl _ => pure ()
        | Sum.inr x' => return x'
      | none => pure ()
    return none
    -- -- buffer ops can have a non contiguous shapetracker
    -- if self.op in GroupOp.Buffer and len(src_sts:=[unwrap(x.st) for x in self.src if x.op is Ops.VIEW]) != 0: return src_sts[0]
    -- if len(src_sts:=[x.st for x in self.src if x.st is not None]) == 0: return None
    -- assert all_same([x.shape for x in src_sts]), f"UOp parents must have the same shape {self} {[x.shape for x in src_sts]}"
    -- # all other ops have a contiguous shapetracker
    -- return ShapeTracker.from_shape(src_sts[0].reduce(self.axis_arg) if self.op in (Ops.REDUCE_AXIS, Ops.WMMA) else src_sts[0].shape)

end UOp
-- UOp methods that depend on ShapeTracker
