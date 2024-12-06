import TeryGrad.Ops.basic

namespace LazyBuffer
def alu : LazyBuffer → Ops → List LazyBuffer → LazyBuffer := sorry
def const_like : LazyBuffer → ConstLike → LazyBuffer := sorry
instance : MathTrait LazyBuffer := {
  alu := alu, const_like := const_like
}
end LazyBuffer
