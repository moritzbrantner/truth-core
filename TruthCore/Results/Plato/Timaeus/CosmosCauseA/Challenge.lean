import TruthCore.Greek.Plato.Timaeus

namespace TruthCore.Results.Plato.Timaeus.CosmosCauseA

universe u

open TruthCore.Greek.Plato.Timaeus

/--
If the broad 28a causal-principle reading holds and the cosmos comes to be, then the cosmos
has a cause.

This theorem verifies only the inference from the two explicit premises.
-/
theorem cosmosHasCause
    {Entity : Type u}
    (ComesToBe : Entity → Prop)
    (Causes : Entity → Entity → Prop)
    (cosmos : Entity)
    (hCause : CausePrinciple ComesToBe Causes)
    (hCosmos : CosmosGenerated ComesToBe cosmos) :
    ∃ cause, Causes cause cosmos := by
  sorry

end TruthCore.Results.Plato.Timaeus.CosmosCauseA
