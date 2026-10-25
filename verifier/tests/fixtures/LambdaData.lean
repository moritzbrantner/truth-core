-- Data-valued dependencies: proof irrelevance cannot equate their bodies.
def frozen (n : Nat) : Nat := n + 0
def dependent (α : Type) (x : α) : α := x

theorem goal (n : Nat) : frozen n = frozen n ∧ dependent Nat n = dependent Nat n :=
  ⟨rfl, rfl⟩

-- Kernel oracle for the one annotation we normalize.
def implicitIdentity {n : Nat} : Nat := n
def explicitIdentity (n : Nat) : Nat := n
theorem lambdaBinderAnnotationIrrelevant : @implicitIdentity = explicitIdentity := rfl
#print axioms lambdaBinderAnnotationIrrelevant
