import TeryGrad.Ops.basic
import TeryGrad.Ops.U
import TeryGrad.Ops.MathTrait
import TeryGrad.Shape.View

def views_to_indexed_uops (views: List View) (_idxs:Option (List UOp) := None) : UOp × UOp :=
  sorry
def views_to_real_strides (views: List View) (ignore_valid : Bool := false) : List (Option SInt) :=
 sorry

structure ShapeTracker :=
  views : List View

namespace ShapeTracker

instance : Add ShapeTracker := sorry

def invert (self : ShapeTracker) (out_shape: List SInt) : Option ShapeTracker := sorry
def from_shape (shape : List SInt) : ShapeTracker := sorry
def contiguous (self : ShapeTracker) : Bool := sorry
def consecutive (self : ShapeTracker) : Bool := sorry
def shape (self : ShapeTracker) : List SInt := sorry
def size (self : ShapeTracker) : Int := sorry
def reduce (self : ShapeTracker) (axis : List Int) : List SInt := sorry
def to_uop (self : ShapeTracker) : UOp := sorry
def to_indexed_uops (self : ShapeTracker) (_idxs: Option (List UOp) := none) : UOp × UOp := sorry
def real_size (self : ShapeTracker) : Int := sorry

variable { α : Type u } [Set α Variable]
def vars (self : ShapeTracker) : α := sorry
variable { β : Type v } [Map β Variable Int]
def var_vals (self : ShapeTracker) : β := sorry
def unbind (self : ShapeTracker) : ShapeTracker × β := sorry

def real_strides (self : ShapeTracker) (ignore_valid : Bool := false) : List (Option SInt) := sorry
def unit_stride_axes (self : ShapeTracker) (ignore_valid : Bool := false) : List Int := sorry

def axis_is_masked (self : ShapeTracker) (axis : Int) : Bool := sorry
def simplify (self : ShapeTracker) : ShapeTracker := sorry

-- *** under this line are the movement ops ***

def pad (self : ShapeTracker) (arg: List (SInt × SInt)) : ShapeTracker := sorry
def shrink (self : ShapeTracker) (arg: List (SInt × SInt)) : ShapeTracker := sorry
def expand (self : ShapeTracker) (new_shape : List SInt) : ShapeTracker := sorry
def permute (self : ShapeTracker) (axis: List Int) : ShapeTracker := sorry
def stride (self : ShapeTracker) (mul: List Int) : ShapeTracker := sorry

def reshape (self : ShapeTracker) (new_shape: List SInt) : ShapeTracker := sorry

end ShapeTracker
