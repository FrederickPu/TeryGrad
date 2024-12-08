import TeryGrad.Ops.basic
import TeryGrad.Ops.MathTrait

instance : BEq SInt := sorry

def canonicalize_strides (shape: List SInt) (strides: List SInt) : List SInt :=
  (shape.zip strides).map (fun ⟨s, st⟩ => if s == (1:Int) then (0:Int) else st)
def strides_for_shape (shape : List SInt) : List SInt := sorry
def _merge_dims (shape : List Int) (strides : List Int) (mask : Option (List (Int × Int)) := none) : List (Int × Int × Int) := sorry
def _reshape_mask (_mask: Option (List (SInt × SInt))) (old_shape: List SInt) (new_shape: List SInt) :
  Option (List (SInt × SInt)) :=
    sorry

def un1d (shape:List SInt) (offs:SInt) : List SInt :=
  sorry

namespace View

def t (self : View) : List SInt := sorry
instance : LT SInt := sorry -- this should be TeryGrad.Ops.basic
instance : LT View := ⟨fun x y => x.t < y.t⟩

def to_indexed_uops (self : View) (_idxs: Option (List UOp ⊕ List UOp) := None) (vexpr: UOp := UOp.const DType.bool true) : UOp × UOp :=
  sorry
def size (self : View) : Int :=
  sorry
def create (shape: List SInt) (strides: Option (List SInt) := none) (offset: SInt := (0:Int)) (mask: Option (List (SInt × SInt)) := none) : View :=
  sorry
variable { α : Type u } [Set α Variable]
def vars (self : View) : α := sorry
variable { β : Type v } [Map β Variable Int]
def unbind (self : View) : View × β := sorry
instance : HAdd View View (Option View) := sorry
def invert (self : View) (out_shape : (List SInt)) : Option View := sorry
def minify (self : View) : View := sorry
def __unsafe_resize (self : View) (arg: List (SInt × SInt)) (mask : Option (List (SInt × SInt)) := none) : View := sorry
def pad (self : View) (arg: List (SInt × SInt)) : View := sorry
def shrink (self : View) (arg: List (SInt × SInt)) : View := sorry

end View
