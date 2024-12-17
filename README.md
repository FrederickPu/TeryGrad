# TeryGrad

An implmentation of the [TinyGrad](https://github.com/tinygrad/tinygrad) kernel in Lean4 with the aim having verified convergence of training algorithms using theorems from the [CertiGrad](https://github.com/dselsam/certigrad/) project.

# benefits

better overall type safety:
- The behavior of the SimpleMathTrait type is much more explicit
potential for formally verified correctness.
- We can require that new function definitions must prove that they satisfy the preconditions of stochastic gradient descent via a Sigma type.
- Shape matching can be enforced as a type constraint. Meanning that shape errors show up as type errors. This has the additional benefit of bypassing the need for a dedicated shape inference engine. Since we can use lean's type inference engine to do the work. For example in tinygrad you would do (-1, 2, 3) but in terygrad you would do [_, 2, 3] (using the hole command to indicate that lean should try to infer the value of _ at elaboration/compile time)

Just as how TinyGrad's size allows it to implement accelerators quickly, TeryGrad's verification abilities allow new models to implmeented quickly with guaranteed convergence properties

# applications for Categorial ML
Lean's flexible type system allows us to define a more general gradient based training algorithms where a model $M_{\theta}$ is parametrized by $\theta \in T$ where $T$ is a additive monoid and has gradient $T'$ where $T'$ is an additive group. Just as a tinygrad can write custom backends for different hardware targets, TeryGGrad will be able to write custom training algorithms for different scalars ($T$) and gradients ($T'$).

# resources

https://github.com/mesozoic-egg/tinygrad-notes/

see TeryGrad/Minimal for implmentation of a simplified version of TinyGrad (so you can see how all the moving parts come together)