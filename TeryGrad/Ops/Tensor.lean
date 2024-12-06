import TeryGrad.Ops.basic

namespace Tensor
def alu : Tensor → Ops → List Tensor → Tensor := sorry
def const_like : Tensor → ConstLike → Tensor := sorry
instance : SimpleMathTrait Tensor := ⟨alu, const_like⟩
end Tensor
