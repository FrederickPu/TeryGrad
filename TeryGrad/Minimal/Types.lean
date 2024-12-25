import Batteries.Logic
#check Array

/- analagoues to np.ndarray
   `NArray shape` is the type np.ndarrays with shape `shape`
-/
inductive NArray (α : Type u) : List Nat → Type u where
| nil (l : List Nat) : NArray α (0::l)
| cons₁ {n : Nat} (a : α) (L : NArray α [n]) : NArray α [n + 1]
| cons₂ {n m : Nat} {l : List Nat} (a : NArray α (m::l)) (L : NArray α (n::(m::l))) : NArray α ((n + 1)::(m::l))

namespace NArray

def toList₁ {α : Type u} {n : Nat} : NArray α [n] → List α
| nil [] => []
| cons₁ a l => a::l.toList₁

def toList₂ {α : Type u} {n m : Nat} {s : List Nat} : NArray α (n::m::s) → List (NArray α (m::s))
| nil _ => []
| cons₂ a l => a::l.toList₂

@[specialize] def map {α : Type u} {β : Type v} {s : List Nat} (f : α → β) : NArray α s → NArray β s
| nil _ => nil _
| cons₁ a l => cons₁ (f a) (l.map f)
| cons₂ a l => cons₂ (a.map f) (l.map f)

@[specialize] def zipWith {α : Type u} {β : Type v} {γ : Type w} {s : List Nat} (f : α → β → γ) : NArray α s → NArray β s → NArray γ s
| cons₁ x xs, cons₁ y ys => cons₁ (f x y) (zipWith f xs ys)
| cons₂ x xs, cons₂ y ys => cons₂ (zipWith f x y) (zipWith f xs ys)
| nil _, nil _ => nil _

def zip {α : Type u} {β : Type v} {s : List Nat} : NArray α s → NArray β s → NArray (Prod α β) s :=
  zipWith Prod.mk

private def aux {α : Type u} [ToString α] {s : List Nat} : NArray α s → String
| NArray.nil n  => ""
| NArray.cons₁ a (NArray.nil []) => toString a
| NArray.cons₁ a l => toString a ++ ", " ++ aux l
| NArray.cons₂ a (NArray.nil _)=> "[" ++ aux a ++ "]"
| NArray.cons₂ a l => "[" ++ aux a  ++ "]" ++ ", " ++ aux l

instance  {α : Type u} [ToString α] {l : List Nat} : ToString (NArray α l) :=
  ⟨fun x => "[" ++ aux x ++ "]"⟩

infixr:67 " :: " => NArray.cons₁
infixr:67 " :: " => NArray.cons₂

syntax "N[" term,* "]" : term

macro_rules
  | `(N[]) => `(NArray.nil _)
  | `(N[N[$xs,*]]) => `(NArray.cons₂ N[$xs,*] (NArray.nil _))
  | `(N[N[$xs,*], $ys,*]) => `(NArray.cons₂ N[$xs,*] N[$ys,*])
  | `(N[$x]) => `(NArray.cons₁ $x (NArray.nil _))
  | `(N[$x, $xs,*]) => `(NArray.cons₁ $x N[$xs,*])

end NArray

/-
    an array of things where the ith thing has shapes[i]
    meant to provided type safety to the notion of tuple of tensors used for parents and save_tensors in tinygrad.
    Note: we use List for the individual shapes since shapes aren't supposed to be mutable (like tuples in python).
-/
structure ShapedVector {Shape : Type v} (ShapedType : Shape → Type u) (shapes : Array Shape) where
    shapedArray : Array (Sigma (fun shape : Shape => ShapedType shape))
    -- we use this definition instead of the quantifier definition for the constructor so that shape matching can be provided using `rfl`
    shapesMatch : shapedArray.map (fun x => x.1) = shapes

def ShapedVector.shapedVector {Shape : Type v} {ShapedType : Shape → Type u} {shapes : Array Shape} : ShapedVector ShapedType shapes → Vector (Sigma (fun shape : Shape => ShapedType shape)) shapes.size
| ⟨shapedArray, shapesMatch⟩ => ⟨shapedArray, by simp [← shapesMatch]⟩

def ShapedVector.hasShape {Shape : Type v} {ShapedType : Shape → Type u} {shapes : Array Shape} (s : ShapedVector ShapedType shapes) :
    ∀ i : Fin (shapes.size), (s.shapedVector.get i).1 = shapes[i] := by
        intro i
        simp [ShapedVector.shapedVector, ← s.shapesMatch]
        rfl

def ShapedVector.get {Shape : Type v} (ShapedType : Shape → Type u) (shapes : Array Shape) (s : ShapedVector ShapedType shapes) (i : Fin shapes.size) :
    ShapedType shapes[i] := by
        rw [← s.hasShape i]
        have : shapes.size = s.shapedArray.size := by
            have := s.shapesMatch
            simp [← this]
        exact s.shapedArray[i].snd

abbrev ShapedNArrayVector (α : Type u) := ShapedVector (NArray α)

/-
   api carrying code for tinygrad's Function class
   if you have Z = X * Y, then the function Z will have parents X and Y

   Technically: init, forward and backward can be computed together in that order.
   However, spliting up into multiple stages allows us to more closely follow the tinygrad codebase.
   Additionally, it might allow us to take advantage of certain caching properties of the lean compiler and ir optimizer.

   We omit the init function since it only initializes the parents. We instead pass parents into the forward pass to have a better type signature for FunctionCtx.
-/
structure EFunction (α : Type u) (β : Type v) (shapes : Array (List Nat)) (outShape : List Nat) where
    saveShapes : Array (List Nat)
    -- take in a context and data tensors (α) to produce an output tensor and array of saved_tensors
    forward : (parents : ShapedNArrayVector α shapes) → NArray α outShape × (ShapedNArrayVector β saveShapes)
    -- computes the gradient based on the saved_tensors in the FunctionCtx
    backward (parents : ShapedNArrayVector α shapes) (saved_tensors : ShapedNArrayVector β saveShapes)
        (grad_output : NArray β outShape) : ShapedNArrayVector β shapes
    -- TODO :: add an additional condition that assures forward and backward compose properly

/- Data carrying part of ComputedAutoDiffTree
-/
protected inductive ComputedAutoDiffTree.DiffTree (α : Type u) (β : Type v) : List Nat → Type (max u v)
| mk
    {outShape : List Nat}
    (parents : Array (Σ shape, ComputedAutoDiffTree.DiffTree α β shape))
    (saved_tensors : Σ shapes, ShapedVector (NArray β) shapes)
    (ctx : Σ shapes, EFunction α β shapes outShape)
    (data : NArray α outShape)
    (grad : NArray β outShape)
    : ComputedAutoDiffTree.DiffTree α β outShape


/- parents, saved_tensors and ctx shapes match at all levels
-/
protected inductive ComputedAutoDiffTree.DiffTree.valid {α : Type u} {β : Type v} : ∀ {shape : List Nat}, ComputedAutoDiffTree.DiffTree α β shape → Prop
| mk {outShape : List Nat} {parents : Array (Σ shape, ComputedAutoDiffTree.DiffTree α β shape)} {saved_tensors : Σ shapes, ShapedVector (NArray β) shapes} {ctx : Σ shapes, EFunction α β shapes outShape} {tensor : NArray α outShape} (grad : NArray β outShape) :
    (parents.map (fun x => x.1) = ctx.1) → (saved_tensors.1 = ctx.2.saveShapes) → (∀ x ∈ parents, x.2.valid) → (ComputedAutoDiffTree.DiffTree.mk parents saved_tensors ctx tensor grad).valid

/-
    AutoDiffTree where the saved_tensors and grad are computed
-/
structure ComputedAutoDiffTree (α : Type u) (β : Type v) (shape : List Nat) where
    diffTree : ComputedAutoDiffTree.DiffTree α β shape
    isValid : diffTree.valid

/- Data carrying part of ForwardedAutoDiffTree
-/
protected inductive ForwardedAutoDiffTree.DiffTree (α : Type u) (β : Type v) : List Nat → Type (max u v)
| mk
    {outShape : List Nat}
    (parents : Array (Σ shape, ForwardedAutoDiffTree.DiffTree α β shape))
    (saved_tensors : Σ shapes, ShapedVector (NArray β) shapes)
    (ctx : Σ shapes, EFunction α β shapes outShape)
    (data : NArray α outShape)
    : ForwardedAutoDiffTree.DiffTree α β outShape

/- parents, saved_tensors and ctx shapes match at all levels
-/
protected inductive ForwardedAutoDiffTree.DiffTree.valid {α : Type u} {β : Type v} : ∀ {shape : List Nat}, ForwardedAutoDiffTree.DiffTree α β shape → Prop
| mk {outShape : List Nat} {parents : Array (Σ shape, ForwardedAutoDiffTree.DiffTree α β shape)} {saved_tensors : Σ shapes, ShapedVector (NArray β) shapes} {ctx : Σ shapes, EFunction α β shapes outShape} {tensor : NArray α outShape} :
    (parents.map (fun x => x.1) = ctx.1) → (saved_tensors.1 = ctx.2.saveShapes) → (∀ x ∈ parents, x.2.valid) → (ForwardedAutoDiffTree.DiffTree.mk parents saved_tensors ctx tensor).valid

/-
    AutoDiffTree where the saved_tensors are computed
-/
structure ForwardedAutoDiffTree (α : Type u) (β : Type v) (shape : List Nat) where
    diffTree : ForwardedAutoDiffTree.DiffTree α β shape
    isValid : diffTree.valid

/- Data carrying part of AutoDiffTree
-/
protected inductive AutoDiffTree.DiffTree (α : Type u) (β : Type v) : List Nat → Type (max u v)
| mk
    {outShape : List Nat}
    (parents : Array (Σ shape, AutoDiffTree.DiffTree α β shape))
    (ctx : Σ shapes, EFunction α β shapes outShape)
    : AutoDiffTree.DiffTree α β outShape

/- parents and ctx shapes match at all levels. all ComputedAutoDiffTree.DiffTree are also valid
-/
inductive AutoDiffTree.DiffTree.valid {α : Type u} {β : Type v} : ∀ {shape : List Nat}, AutoDiffTree.DiffTree α β shape → Prop
| mk (parents : Array (Σ shape, AutoDiffTree.DiffTree α β shape)) (ctx : Σ shapes, EFunction α β shapes outShape) : (parents.map (fun x => x.1) = ctx.1) → (∀ x ∈ parents, x.2.valid) → (AutoDiffTree.DiffTree.mk parents ctx).valid

/-
    simplified version of computation graph (no weight sharing)
    AutoDiffTree α β outShape
-/
structure AutoDiffTree (α : Type u) (β : Type v) (shape : List Nat) where
    diffTree : AutoDiffTree.DiffTree α β shape
    isValid : diffTree.valid

namespace AutoDiffTree

def init {shapes : Array (List Nat)} {outShape : List Nat} (parents : ShapedVector (AutoDiffTree α β) shapes) (ctx : EFunction α β shapes outShape) : AutoDiffTree α β outShape := sorry

variable {α α₁ α₂ : Type u₁} {β : α → Type u₂} {β₁ : α₁ → Type u₃} {β₂ : α₂ → Type u₄}
@[simp] -- @[nolint simpNF]
theorem Sigma.mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  ⟨fun h ↦ by cases h; simp,
   fun ⟨h₁, h₂⟩ ↦ by subst h₁; rw [eq_of_heq h₂]⟩

instance {α : Type u} {β : Type v} {shape : List Nat}  : Inhabited (ForwardedAutoDiffTree α β shape) := sorry

partial def forward {α : Type u} {β : Type v} {shape : List Nat} : AutoDiffTree α β shape → ForwardedAutoDiffTree α β shape
| ⟨AutoDiffTree.DiffTree.mk (parents : Array (Σ shape, AutoDiffTree.DiffTree α β shape)) (ctx : Σ shapes, EFunction α β shapes shape), h⟩ => by
    let parents' : Array (Σ shape', ForwardedAutoDiffTree α β shape') := parents.attach.map (fun ⟨⟨shape', tree⟩, h'⟩ => ⟨shape',
        forward { diffTree := tree, isValid := by {
            cases h
            have wee : ∀ (x : (shape : List Nat) × AutoDiffTree.DiffTree α β shape), x ∈ parents → x.snd.valid := by trivial
            exact wee ⟨shape', tree⟩ h'
        }}⟩)
    let parentsTensors : Array (Σ shape, NArray α shape) := parents'.map (fun ⟨shape', fnCtx'⟩ => (⟨shape',
        let w : fnCtx'.diffTree.1 = shape' := by
            cases fnCtx'.diffTree
            simp
        cast (by rw [w]) fnCtx'.diffTree.5
    ⟩))
    have :  Array.map (fun x => x.fst) parents = ctx.fst := by
        cases h
        trivial
    let parentsTensors : ShapedNArrayVector α ctx.1 := ⟨parentsTensors, by {
        cases h
        rw [← this]
        ext i h1 h2 : 1
        all_goals simp [parentsTensors, parents']
    }⟩
    let ⟨tensor, saved_tensors⟩ := ctx.2.forward parentsTensors
    exact ⟨⟨parents'.map (fun x => ⟨x.1, x.2.1⟩), ⟨_, saved_tensors⟩, ctx, tensor⟩, by {
        apply ForwardedAutoDiffTree.DiffTree.valid.mk
        simp [parents', this]
        simp; intro ⟨shapeX, X⟩ hX
        simp; simp at hX
        match hX with
        | ⟨⟨shapeP, P⟩, hp, H⟩ =>
            cases H.1
            cases H.2
            exact P.isValid
    }⟩
-- termination_by
--     t => sizeOf t
-- decreasing_by
--     simp
--     have := Array.sizeOf_lt_of_mem h'
--     simp at this
--     omega


end AutoDiffTree

namespace ForwardedAutoDiffTree

#check List.enum
#check ComputedAutoDiffTree.DiffTree.mk

instance {α : Type u} {β : Type v} {shape : List Nat}  : Inhabited (ComputedAutoDiffTree α β shape) := sorry

partial def backward {α : Type u} {β : Type v} {shape : List Nat} : ForwardedAutoDiffTree α β shape → NArray β shape → ComputedAutoDiffTree α β shape
| ⟨ForwardedAutoDiffTree.DiffTree.mk (parents : Array (Σ shape, ForwardedAutoDiffTree.DiffTree α β shape)) (saved_tensors : Σ shapes, ShapedVector (NArray β) shapes) (ctx : Σ shapes, EFunction α β shapes shape) (data : NArray α shape), h⟩, grad_output => by {
    let ⟨grads, gradsVal⟩ := ctx.2.backward ⟨parents.map (fun x => ⟨x.2.1, x.2.5⟩), sorry⟩ (cast sorry saved_tensors) grad_output
    let parents' : Array (Σ shape, ComputedAutoDiffTree.DiffTree α β shape) := List.toArray <| parents.toList.enum.map (fun ⟨i, x⟩ => ⟨x.1, ((⟨x.2, sorry⟩ : ForwardedAutoDiffTree α β x.1).backward (cast sorry (grads.get i sorry).2)).1⟩)
    exact ⟨⟨parents', saved_tensors, ctx, data, grad_output⟩, sorry⟩
}
end ForwardedAutoDiffTree

variable {α : Type u} {β : Type v}

/-!
    Consider the following example:
    ```python
    class TinyBobNet:
        def __init__(self):
            self.l1 = Tensor(layer_init(784, 128))
            self.l2 = Tensor(layer_init(128, 10))

        def forward(self, x):
            return x.dot(self.l1).relu().dot(self.l2).logsoftmax()
    ```
    In training, TinyBobNet.forward is called with a fresh tensor
    ```python
    samp = np.random.randint(0, X_train.shape[0], size=(BS))
    x = Tensor(X_train[samp].reshape((-1, 28*28)))
    ```
    Additionally recall that apply looks like this
    ```python
    def apply(self, arg, *x):
        ctx = arg(self, *x)
        ret = Tensor(arg.forward(ctx, self.data, *[t.data for t in x]))
        ret._ctx = ctx
        return ret
    ```
    At each training step. Meaning that at each training step:
    - x has a fresh context
    - so when you run x.dot(self.l1), the corresponding call to apply a Tensor with a fresh context is returned.
    And this proces just keeps going. Importantly, the weights layers l1, l2 don't carry any context information.
    Meaning that each iterations context is compltely independent of the previous iteration's context.
-/

instance {α : Type u} [Inhabited α] : Inhabited ((shape : List Nat) × (NArray α shape)) :=
    ⟨[0], NArray.nil []⟩

instance {α : Type u} {shape : List Nat} [Add α] : Add (NArray α shape) :=
    ⟨fun x y => NArray.zipWith (· + ·) x y⟩
instance {α : Type u} {shape : List Nat} [Mul α] : Mul (NArray α shape) :=
    ⟨fun x y => NArray.zipWith (· * ·) x y⟩

def add {α : Type u} [Inhabited α] [Add α] {β : Type v} (shape : List Nat): EFunction α β #[shape, shape] shape :=
{
    saveShapes := #[]
    forward :=
     fun parents =>
        let x1 : NArray α shape := cast (by simp [parents.hasShape]; rfl) (parents.shapedVector.get ⟨0, by simp⟩).2
        let x2 : NArray α shape := cast (by simp [parents.hasShape]; rfl) (parents.shapedVector.get ⟨1, by simp⟩).2
        ⟨x1 + x2, ⟨#[], rfl⟩⟩
    backward := fun parents saved_tensors grad_output =>
        ⟨#[⟨shape, grad_output⟩, ⟨shape, grad_output⟩], rfl⟩
}

def mul (α : Type u) [Inhabited α] [Add α] [Mul α] (shape : List Nat): EFunction α α #[shape, shape] shape :=
{
    saveShapes := #[shape, shape]
    forward :=
     fun parents =>
        let x1 : NArray α shape := cast (by simp [parents.hasShape]; rfl) (parents.shapedVector.get ⟨0, by simp⟩).2
        let x2 : NArray α shape := cast (by simp [parents.hasShape]; rfl) (parents.shapedVector.get ⟨1, by simp⟩).2
        ⟨x1 * x2, ⟨#[⟨shape, x1⟩, ⟨shape, x2⟩], rfl⟩⟩
    backward := fun parents saved_tensors grad_output =>
        let x1 : NArray α shape := cast (by simp [saved_tensors.hasShape]; rfl) (saved_tensors.shapedVector.get ⟨0, by simp⟩).2
        let x2 : NArray α shape := cast (by simp [saved_tensors.hasShape]; rfl) (saved_tensors.shapedVector.get ⟨1, by simp⟩).2
        ⟨#[⟨shape, grad_output * x1⟩, ⟨shape, grad_output * x2⟩], rfl⟩
}

#check Vector
