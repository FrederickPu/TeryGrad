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

/-
    an array of tensors where the ith tensor has shapes[i]
    meant to provided type safety to the notion of tuple of tensors used for parents and save_tensors in tinygrad.
    Note: we use List for the individual shapes since shapes aren't supposed to be mutable (like tuples in python).
-/
structure ShapedTensorVector (α : Type u) (shapes : Array (List Nat)) where
    tensorVector : Vector (Sigma (fun shape : List Nat => Tensor α shape)) shapes.size
    hasShape : ∀ i : Fin shapes.size, (tensorVector.get i).1 = shapes[i]

def ShapedTensorVector.get {α : Type u} {shapes : Array (List Nat)} (x : ShapedTensorVector α shapes) (i : Fin shapes.size) :
    Tensor α shapes[i] := by
        rw [← x.hasShape i]
        exact x.tensorVector[i].snd

/-
    Tensor but with additional autograd information.
    The `E` stands for `ε` from the dual numbers.
    Note that we support different types for the data and grad tensors
    since there are some cases where grad needs for precision / structure than data.
    For example α could be a Monoid while β could be a group.
-/
structure ETensor (α : Type u) (β : Type v) (shape : List Nat) where
    data : Tensor α shape
    grad : Option (Tensor β shape)

structure DVector {n : Nat} (p : Fin n → Type u) where
  val : (i : Fin n) → p i

/-
   Context for gradient information during autograd.
   The data-carrying part of tinygrad's Function class.
   As with ETensor
   - α is the data type
   - β is the grad type
-/
structure FunctionCtx (α : Type u) (β : Type v) (numParents : Nat) (saveShapes : Array (List Nat)) where
    parents : Vector ((shape : List Nat) × (ETensor α β shape)) numParents
    saved_tensors : ShapedTensorVector β saveShapes

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
    -- take in a context and data tensors (α) to produce an output tensor and function context
    forward : (parents : Vector ((shape : List Nat) × (ETensor α β shape)) shapes.size) → ShapedTensorVector α shapes → Tensor α outShape × FunctionCtx α β shapes.size saveShapes
    -- computes the gradient based on the saved_tensors in the FunctionCtx
    backward : FunctionCtx α β shapes.size saveShapes → Tensor β outShape → ShapedTensorVector β shapes
    -- TODO :: add an additional condition that assures forward and backward compose properly

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
def add (α : Type u) [Inhabited α] [Add α] (β : Type v) [Add β] (shape : List Nat): EFunction α β #[shape, shape] shape :=
{
    saveShapes := #[]
    forward :=
     fun parents x =>
        let x1 : Tensor α shape := x.get ⟨0, by simp⟩
        let x2 : Tensor α shape := x.get ⟨1, by simp⟩
        ⟨x1 + x2, ⟨parents, ⟨#v[], fun ⟨i, hi⟩ => by simp at hi⟩⟩⟩
    backward := fun ⟨parents, saved_tensors⟩ grad_output => Id.run do
        ⟨⟨#[⟨shape, grad_output⟩, ⟨shape, grad_output⟩], by simp⟩,
            by {
                intro i
                match i with
                | ⟨i, hi⟩ => {
                    simp at hi
                    match i with
                    | 0 => rfl
                    | 1 => rfl
                }
            }⟩
}

#check Vector
