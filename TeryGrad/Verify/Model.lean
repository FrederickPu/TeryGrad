/--
  In this file we will sketch the Guarantee API.
  Which allows models with guaranteed convergence to be constructed and composed easily.
-/
inductive Model
-- other stuff (tbd)
| comp : Model → Model → Model

/--
  A Guarantee is basically a predicate on a Model but with the additional condition
  that composing Models satisfying a guaranteed will result in a model that also satisfies the guarantee
-/
structure Guarantee :=
  pred : Model → Prop
  comp : ∀ x y : Model, pred x → pred y → pred (x.comp y)

/--
  The type of all models satifying a given guaranteed
-/
structure ModelGuarantee (g : Guarantee) :=
  model : Model
  guarantee : g.pred model
