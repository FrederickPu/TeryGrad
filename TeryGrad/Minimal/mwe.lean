example (A B : Array Nat) : A = B := by
    ext i h1 h2


/- case h₁
    A B : Array Nat
    ⊢ A.size = B.size
case h₂
    A B : Array Nat
    i✝ : Nat
    hi₁✝ : i✝ < A.size
    hi₂✝ : i✝ < B.size
    ⊢ A[i✝] = B[i✝]
-/
