module

public import TruthCore.Causality.ActualFusionNecessaryBeing

/-! Controls for the existing local actual-part policy. The full Nat candidate
carrier and its usual order are retained. No causal policy or reality claim is
inferred from this interpretation. -/

@[expose] public section

namespace TruthCore.Causality.ActualPartsDeclarationControls
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualFusionNecessaryBeing

/-- All candidates exist at false; only positive candidates exist at true.
Accessibility is universal and the primitive causal relation has no edges. -/
def model : Ontic Bool Nat where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => w = false ∨ 0 < x
  Causes := fun _ _ _ => False

/-- The original local policy is inhabited, with actual wholes and parts. -/
theorem localParts : ActualPartsExistAt model false := by
  intro x p _ _
  exact Or.inl rfl

/-- Local closure is not world-uniform closure: 0 is part of actual 1 at true,
but is absent there. This is a counterinterpretation, not a metaphysical claim. -/
theorem notRemoteParts : ¬ ActualPartsExistAt model true := by
  intro h
  have absent := h 1 0 (Or.inr (by decide)) (by decide)
  rcases absent with impossible | impossible <;> cases impossible

/-- This control does not obtain a necessary being by defining a cause. -/
theorem noCause (w : Bool) (c x : Nat) : ¬ model.Causes w c x := by
  intro h
  exact h

end TruthCore.Causality.ActualPartsDeclarationControls
