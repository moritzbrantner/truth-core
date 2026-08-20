import TruthCore.Greek.Plato.Timaeus

namespace TruthCore.Results.Plato.Timaeus.CosmosCauseB

universe u

open TruthCore.Greek.Plato.Timaeus

/--
If the stronger distinct-cause reading of 28a holds and the cosmos comes to be, then there is
some cause of the cosmos distinct from the cosmos.

This is intentionally a separate result rather than treating distinctness as implicit in the
broader interpretation.
-/
theorem cosmosHasDistinctCause
    {Entity : Type u}
    (ComesToBe : Entity → Prop)
    (Causes : Entity → Entity → Prop)
    (cosmos : Entity)
    (hCause : DistinctCausePrinciple ComesToBe Causes)
    (hCosmos : CosmosGenerated ComesToBe cosmos) :
    ∃ cause, cause ≠ cosmos ∧ Causes cause cosmos := by
  sorry

end TruthCore.Results.Plato.Timaeus.CosmosCauseB
