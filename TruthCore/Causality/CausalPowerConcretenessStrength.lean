module

public import TruthCore.Causality.CausalPowerConcreteness

/-!
# Strong version of the causal-power concreteness principle (#1103, #1017)

The owner approved only the WEAK version, `OwnerCommitmentAt`: efficient
causes (`Ontic.Causes`) and bearers of causal power are concrete. The strong
version adds every other supplied causal sense (`otherCauses s`, e.g. formal,
final, exemplar or explanatory causation). It is recorded as a separate, NOT
approved sibling. It would conflict with exemplar causation on the Fourth Way
route and with Aristotelian formal and final causes, where the cause need not be
a concrete individual.
-/

@[expose] public section

namespace TruthCore.Causality.CausalPowerConcretenessStrength

open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.CausalPowerConcreteness (OwnerCommitmentAt)

/-- Strong version: the weak commitment together with "every cause in every
other supplied causal sense is concrete". -/
def AllCausalSensesRequireConcreteAt {W B Sense : Type} (o : Ontic W B)
    (otherCauses : Sense → W → B → B → Prop) (concrete : B → Prop)
    (hasCausalPower : W → B → Prop) (w : W) : Prop :=
  OwnerCommitmentAt o concrete hasCausalPower w ∧
    ∀ s x y, otherCauses s w x y → concrete x

end TruthCore.Causality.CausalPowerConcretenessStrength
