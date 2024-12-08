import TeryGrad.Ops.basic
import TeryGrad.DType
import TeryGrad.Shape.ShapeTracker

inductive LazyBuffer
| mk
  (device : String)
  (shapeTracker : ShapeTracker)
  (dtype : DType)
  (op : Option Ops)
  (arg: Option (ConstType ⊕ UOp ⊕ List ConstType))
  (srcs : List LazyBuffer)
  (base: Option LazyBuffer)
  (metadata: Option Int)

namespace LazyBuffer
def default (device : String) (st : ShapeTracker) (dtype : DType) : LazyBuffer :=
  mk device st dtype none none [] none none
def alu : LazyBuffer → Ops → List LazyBuffer → LazyBuffer := sorry
def const_like : LazyBuffer → ConstLike → LazyBuffer := sorry
instance : MathTrait LazyBuffer := {
  alu := alu, const_like := const_like
}
end LazyBuffer
