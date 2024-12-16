import TeryGrad.Shape.ShapeTracker
import TeryGrad.Ops.U
import TeryGrad.Helpers

namespace UOp

partial def listlize (self:UOp) : ListTree (Int × Option (ConstLike ⊕ ShapeTracker) × Option DType) :=
  ListTree.mk (self.op.value, self.arg, self.dtype) (self.src.map (fun x => x.listlize))

instance : Inhabited UOp := sorry
instance : BEq ShapeTracker := sorry

partial def st (self : UOp) : Option ShapeTracker
:= Id.run do
    if self.op == Ops.VIEW then
      match self.arg with
      | some (Sum.inr x) => return x
      | _ => pure ()
    -- buffer ops can have a non contiguous shapetracker
    if GroupOp.Buffer.contains self.op then
      let src_sts : List ShapeTracker := (self.src.filter (fun x => x.op == Ops.VIEW)).filterMap (fun x => unwrap x.st)
      if src_sts.length != 0 then return src_sts.get! 0
    -- get all non none srcs
    let src_sts : List ShapeTracker := self.src.filterMap (fun x => x.st)
    if src_sts.length == 0 then return none
    -- assert all_same([x.shape for x in src_sts]), f"UOp parents must have the same shape {self} {[x.shape for x in src_sts]}"
    -- buffer ops can have a non contiguous shapetracker
    return ShapeTracker.from_shape (if [Ops.REDUCE_AXIS, Ops.WMMA].contains self.op then (src_sts.get! 0).reduce self.axis_arg else (src_sts.get! 0).shape)
def shape (self : UOp) : List SInt := (unwrap self.st).shape
partial def full_shape (self : UOp) : List SInt :=
  if self.op == Ops.VIEW then self.shape else
    self.src.filter (fun x => x.st.isSome) |>.map (smax ∘ full_shape)
def size (self : UOp) : Int :=
  if self.op == Ops.BUFFER then self.arg[1][1] else (unwrap self.st).size


  -- tuple(smax(x) for x in zip(*[x.full_shape for x in self.src if x.has_st]))
end UOp
-- UOp methods that depend on ShapeTracker
