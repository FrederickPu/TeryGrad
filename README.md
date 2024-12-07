# TeryGrad

An implmentation of the [TinyGrad](https://github.com/tinygrad/tinygrad) kernel in Lean4 with the aim having verified convergence of training algorithms using theorems from the [CertiGrad](https://github.com/dselsam/certigrad/) project.

# benefits

better overall type safety:
- The behavior of the SimpleMathTrait type is much more explicit
potential for formally verified correctness.
- We can require that new function definitions must prove that they satisfy the preconditions of stochastic gradient descent via a Sigma type.
Just as how TinyGrad's size allows it to implement accelerators quickly TeryGrad's verification abilities allow new models to implmeented quickly with guaranteed convergence properties
