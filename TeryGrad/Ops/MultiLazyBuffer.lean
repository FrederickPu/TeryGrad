import TeryGrad.Ops.basic

namespace MultiLazyBuffer
def alu : MultiLazyBuffer → Ops → List MultiLazyBuffer → MultiLazyBuffer := sorry
def const_like : MultiLazyBuffer → ConstLike → MultiLazyBuffer := sorry
instance : MathTrait MultiLazyBuffer := {
  alu := alu, const_like := const_like
}
end MultiLazyBuffer
