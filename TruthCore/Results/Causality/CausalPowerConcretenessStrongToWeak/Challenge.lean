import TruthCore.Causality.CausalPowerConcretenessStrength
namespace TruthCore.Results.Causality.CausalPowerConcretenessStrongToWeak
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.CausalPowerConcreteness (OwnerCommitmentAt)
open TruthCore.Causality.CausalPowerConcretenessStrength
/-- The strong causal-power concreteness principle (every causal sense) entails
the weak one (efficient causation and causal power), which is the owner-approved
floor item. Projection of the first conjunct: the strong version is the weak
one plus a clause about the other causal senses. -/
theorem weakOfStrong {W B Sense : Type} (o : Ontic W B)
    (otherCauses : Sense → W → B → B → Prop) (concrete : B → Prop)
    (hasCausalPower : W → B → Prop) (w : W)
    (hStrong : AllCausalSensesRequireConcreteAt o otherCauses concrete hasCausalPower w) :
    OwnerCommitmentAt o concrete hasCausalPower w := by
  sorry
end TruthCore.Results.Causality.CausalPowerConcretenessStrongToWeak
