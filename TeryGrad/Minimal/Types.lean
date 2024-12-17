#check Array

-- n nested homogenous Array
inductive NArray (α : Type u) : Nat → Type u where
| nil (n : Nat) : NArray α n
| cons₁ (a : α) (l : NArray α 1) : NArray α 1
| cons₂ {n : Nat} (a : NArray α n) (l : NArray α (n+1)) : NArray α (n + 1)

structure Path (shape : List Nat) where
    path : List Nat
    lenLt : path.length < shape.length
    inBounds : ∀ i : Fin path.length, path.get i < shape.get ⟨i.val, Nat.lt_trans i.isLt lenLt⟩

def NArray.depth {α : Type u} {n : Nat} (_ : NArray α n) : Nat := n

def NArray.length {α : Type u} {n : Nat} : (array : NArray α n) → Nat
| nil n => 0
| cons₁ _ l => l.length.succ
| cons₂ _ l => l.length.succ

def NArray.get {α : Type u} {n : Nat} : (array : NArray α n) → (i : Fin array.length) → NArray α (n - 1)
| cons₁ _ _, _ => nil 0
| cons₂ a _,  ⟨0, _⟩ => a
| cons₂ _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩

def NArray.get? {α : Type u} {n : Nat} : (array : NArray α n) → Nat → Option (NArray α (n - 1))
| cons₁ _ _,  _ => some (nil 0)
| cons₂ a _, 0 => some a
| cons₂ _ as, i+1 => get? as i
| _, _ => none

def NArray.at {α : Type u} {n : Nat} (array : NArray α n) : (path : List Nat) → Option (NArray α (n - path.length))
| [] => some array
| a::l => match array.get? a with
          | some x => by {
            have : (n - (a :: l).length) = (n - 1) - l.length := by
                simp [Nat.Simproc.sub_add_eq_comm n l.length 1]
            rw [this]
            exact (x.at l)
          }
          | none => none

def NArray.lengthUniform {α : Type u} {n : Nat} : NArray α n → Prop
| nil n => True
| cons₁ _ _ => True
| cons₂ a l => (∀ x y : Fin (cons₂ a l).length, ((cons₂ a l).get x).length = ((cons₂ a l).get y).length) ∧ (∀ x : Fin (cons₂ a l).length, ((cons₂ a l).get x).lengthUniform)

/-
    NArray where at each depth the elements have the same length
    [[1, 2], [2, 3]] is a Tensor but [[1, 2], [3]] is not
    same np.ndarray
-/
structure Tensor (α : Type u) (shape : List Nat) : Type u where
    (toNArray : NArray α (if shape.isEmpty then 0 else shape.get! 0))
    (matchShape : ∀ n : Fin shape.length,
     ∀ path : Path shape,
      path.path.length = n →
        (toNArray.at path.path) ≠ none ∧
        (toNArray.at path.path).map NArray.length = shape.get n)


structure ShapedVector {Shape : Type v} (ShapedType : Shape → Type u) (shapes : Array Shape) where
    shapedArray : Array (Sigma (fun shape : Shape => ShapedType shape))
    -- we use this definition instead of the quantifier definition for the constructor so that shape matching can be provided using `rfl`
    shapesMatch : shapedArray.map (fun x => x.1) = shapes

def ShapedVector.shapedVector {Shape : Type v} {ShapedType : Shape → Type u} {shapes : Array Shape} : ShapedVector ShapedType shapes → Vector (Sigma (fun shape : Shape => ShapedType shape)) shapes.size
| ⟨shapedArray, shapesMatch⟩ => ⟨shapedArray, by simp [← shapesMatch]⟩
/-
    an array of tensors where the ith tensor has shapes[i]
    meant to provided type safety to the notion of tuple of tensors used for parents and save_tensors in tinygrad.
    Note: we use List for the individual shapes since shapes aren't supposed to be mutable (like tuples in python).
-/
def ShapedTensorVector (α : Type u) := ShapedVector (Tensor α)

def ShapedTensorVector.hasShape {α : Type u} {shapes : Array (List Nat)} (s : ShapedTensorVector α shapes) :
    ∀ i : Fin (shapes.size), (s.shapedVector.get i).1 = shapes[i] := by
        intro i
        simp [ShapedVector.shapedVector, ← s.shapesMatch]
        rfl

def ShapedTensorVector.get {α : Type u} {shapes : Array (List Nat)} (x : ShapedTensorVector α shapes) (i : Fin shapes.size) :
    Tensor α shapes[i] := by
        rw [← x.hasShape i]
        have : shapes.size = x.shapedArray.size := by
            have := x.shapesMatch
            simp [← this]
        exact x.shapedArray[i].snd

structure DVector {n : Nat} (p : Fin n → Type u) where
  val : (i : Fin n) → p i

/-
   api carrying code for tinygrad's Function class
   if you have Z = X * Y, then the function Z will have parents X and Y

   Technically: init, forward and backward can be computed together in that order.
   However, spliting up into multiple stages allows us to more closely follow the tinygrad codebase.
   Additionally, it might allow us to take advantage of certain caching properties of the lean compiler and ir optimizer.

   We omit the finite function since it only initializes the parents. We instead pass parents into the forward pass to have a better type signature for FunctionCtx.
-/
structure EFunction (α : Type u) (β : Type v) (shapes : Array (List Nat)) (outShape : List Nat) where
    saveShapes : Array (List Nat)
    -- take in a context and data tensors (α) to produce an output tensor and array of saved_tensors
    forward : (parents : ShapedTensorVector α shapes) → Tensor α outShape × (ShapedTensorVector β saveShapes)
    -- computes the gradient based on the saved_tensors in the FunctionCtx
    backward (parents : ShapedTensorVector α shapes) (saved_tensors : ShapedTensorVector β saveShapes)
        (grad_output : Tensor β outShape) : ShapedTensorVector β shapes
    -- TODO :: add an additional condition that assures forward and backward compose properly

/- Data carrying part of ComputedAutoDiffTree
-/
protected inductive ComputedAutoDiffTree.DiffTree (α : Type u) (β : Type v) : List Nat → Type (max u v)
| mk
    {outShape : List Nat}
    (parents : Array (Σ shape, ComputedAutoDiffTree.DiffTree α β shape))
    (saved_tensors : Σ shapes, ShapedVector (Tensor β) shapes)
    (ctx : Σ shapes, EFunction α β shapes outShape)
    (tensor : Tensor α outShape)
    : ComputedAutoDiffTree.DiffTree α β outShape

/- parents, saved_tensors and ctx shapes match at all levels
-/
protected inductive ComputedAutoDiffTree.DiffTree.valid {α : Type u} {β : Type v} : ∀ {shape : List Nat}, ComputedAutoDiffTree.DiffTree α β shape → Prop
| mk {outShape : List Nat} {parents : Array (Σ shape, ComputedAutoDiffTree.DiffTree α β shape)} {saved_tensors : Σ shapes, ShapedVector (Tensor β) shapes} {ctx : Σ shapes, EFunction α β shapes outShape} {tensor : Tensor α outShape} :
    (parents.map (fun x => x.1) = ctx.1) → (saved_tensors.1 = ctx.2.saveShapes) → (∀ x ∈ parents, x.2.valid) → (ComputedAutoDiffTree.DiffTree.mk parents saved_tensors ctx tensor).valid

/-
    AutoDiffTree where the saved_tensors are computed
-/
structure ComputedAutoDiffTree (α : Type u) (β : Type v) (shape : List Nat) where
    diffTree : ComputedAutoDiffTree.DiffTree α β shape
    isValid : diffTree.valid

/- Data carrying part of AutoDiffTree
-/
protected inductive AutoDiffTree.DiffTree (α : Type u) (β : Type v) : List Nat → Type (max u v)
| mk
    {outShape : List Nat}
    (parents : Array (Σ shape, AutoDiffTree.DiffTree α β shape))
    (ctx : Σ shapes, EFunction α β shapes outShape)
    : AutoDiffTree.DiffTree α β outShape
| ofComputed {shape : List Nat}: ComputedAutoDiffTree.DiffTree α β shape → AutoDiffTree.DiffTree α β shape

/- parents and ctx shapes match at all levels. all ComputedAutoDiffTree.DiffTree are also valid
-/
inductive AutoDiffTree.DiffTree.valid {α : Type u} {β : Type v} : ∀ {shape : List Nat}, AutoDiffTree.DiffTree α β shape → Prop
| mk (parents : Array (Σ shape, AutoDiffTree.DiffTree α β shape)) (ctx : Σ shapes, EFunction α β shapes outShape) : (parents.map (fun x => x.1) = ctx.1) → (∀ x ∈ parents, x.2.valid) → (AutoDiffTree.DiffTree.mk parents ctx).valid
| ofComputed : computedTree.valid → (ofComputed computedTree).valid

/-
    simplified version of computation graph (no weight sharing)
    AutoDiffTree α β outShape
-/
structure AutoDiffTree (α : Type u) (β : Type v) (shape : List Nat) where
    diffTree : AutoDiffTree.DiffTree α β shape
    isValid : diffTree.valid

namespace AutoDiffTree

def init : False := sorry

variable {α α₁ α₂ : Type u₁} {β : α → Type u₂} {β₁ : α₁ → Type u₃} {β₂ : α₂ → Type u₄}
@[simp] -- @[nolint simpNF]
theorem Sigma.mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  ⟨fun h ↦ by cases h; simp,
   fun ⟨h₁, h₂⟩ ↦ by subst h₁; rw [eq_of_heq h₂]⟩


def forward {α : Type u} {β : Type v} {shape : List Nat} : AutoDiffTree α β shape → ComputedAutoDiffTree α β shape
| ⟨AutoDiffTree.DiffTree.ofComputed c, h⟩ => ⟨c, by {
    cases h
    trivial
}⟩
| ⟨AutoDiffTree.DiffTree.mk (parents : Array (Σ shape, AutoDiffTree.DiffTree α β shape)) (ctx : Σ shapes, EFunction α β shapes shape), h⟩ => by
    let parents' : Array (Σ shape', ComputedAutoDiffTree α β shape') := parents.attach.map (fun ⟨⟨shape', tree⟩, h'⟩ => ⟨shape',
        forward { diffTree := tree, isValid := by {
            cases h
            have wee : ∀ (x : (shape : List Nat) × AutoDiffTree.DiffTree α β shape), x ∈ parents → x.snd.valid := by trivial
            exact wee ⟨shape', tree⟩ h'
        }}⟩)
    let parentsTensors : Array (Σ shape, Tensor α shape) := parents'.map (fun ⟨shape', fnCtx'⟩ => (⟨shape',
        let w : fnCtx'.diffTree.1 = shape' := by
            cases fnCtx'.diffTree
            simp
        cast (by rw [w]) fnCtx'.diffTree.5
    ⟩))
    have :  Array.map (fun x => x.fst) parents = ctx.fst := by
        cases h
        trivial
    let parentsTensors : ShapedTensorVector α ctx.1 := ⟨parentsTensors, by {
        cases h
        rw [← this]
        ext i h1 h2 : 1
        simp [parentsTensors, parents']
        simp [parentsTensors, parents']
    }⟩
    let ⟨tensor, saved_tensors⟩ := ctx.2.forward parentsTensors
    exact ⟨⟨parents'.map (fun x => ⟨x.1, x.2.1⟩), ⟨_, saved_tensors⟩, ctx, tensor⟩, by {
        apply ComputedAutoDiffTree.DiffTree.valid.mk
        simp [parents', this]
        simp
        intro ⟨shapeX, X⟩ hX
        simp
        simp at hX
        match hX with
        | ⟨⟨shapeP, P⟩, hp, H⟩ => {
            simp at H
            have := H.1
            have := H.2
            have := H.2.symm
            sorry
        }
    }⟩
/-
α : Type u
β : Type v
shape✝ : List Nat
parents : Array ((shape : List Nat) × AutoDiffTree.DiffTree α β shape)
ctx : (shapes : Array (List Nat)) × EFunction α β shapes shape✝
tensor : DualTensor α β shape✝
h : (DiffTree.mk parents ctx tensor).valid
shape : List Nat
tree : AutoDiffTree.DiffTree α β shape
⊢ sizeOf tree < 1 + sizeOf shape✝ + sizeOf parents + sizeOf ctx + sizeOf tensor
-/

end AutoDiffTree

namespace ComputedAutoDiffTree
def backward : False := sorry
end ComputedAutoDiffTree

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

instance {α : Type u} [Inhabited α] : Inhabited ((shape : List Nat) × (Tensor α shape)) := sorry

instance {α : Type u} {shape : List Nat} [Add α] : Add (Tensor α shape) := sorry
instance {α : Type u} {shape : List Nat} [Mul α] : Mul (Tensor α shape) := sorry

def add {α : Type u} [Inhabited α] [Add α] {β : Type v} (shape : List Nat): EFunction α β #[shape, shape] shape :=
{
    saveShapes := #[]
    forward :=
     fun parents =>
        let x1 : Tensor α shape := cast (by simp [parents.hasShape]; rfl) (parents.shapedVector.get ⟨0, by simp⟩).2
        let x2 : Tensor α shape := cast (by simp [parents.hasShape]; rfl) (parents.shapedVector.get ⟨1, by simp⟩).2
        ⟨x1 + x2, ⟨#[], rfl⟩⟩
    backward := fun parents saved_tensors grad_output =>
        ⟨#[⟨shape, grad_output⟩, ⟨shape, grad_output⟩], rfl⟩
}

def mul (α : Type u) [Inhabited α] [Add α] [Mul α] (shape : List Nat): EFunction α α #[shape, shape] shape :=
{
    saveShapes := #[shape, shape]
    forward :=
     fun parents =>
        let x1 : Tensor α shape := cast (by simp [parents.hasShape]; rfl) (parents.shapedVector.get ⟨0, by simp⟩).2
        let x2 : Tensor α shape := cast (by simp [parents.hasShape]; rfl) (parents.shapedVector.get ⟨1, by simp⟩).2
        ⟨x1 * x2, ⟨#[⟨shape, x1⟩, ⟨shape, x2⟩], rfl⟩⟩
    backward := fun parents saved_tensors grad_output =>
        let x1 : Tensor α shape := cast (by simp [saved_tensors.hasShape]; rfl) (saved_tensors.shapedVector.get ⟨0, by simp⟩).2
        let x2 : Tensor α shape := cast (by simp [saved_tensors.hasShape]; rfl) (saved_tensors.shapedVector.get ⟨1, by simp⟩).2

        ⟨#[⟨shape, grad_output * x1⟩, ⟨shape, grad_output * x2⟩], rfl⟩
}

#check Vector
