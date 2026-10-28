import TruthCore.German.Kant.CosmologicalInference

/-! A one-way actuality interface for the #319 foundation investigation.
The ontic existence assignment and the supplied act-in-esse predicate retain
their independent meanings. This module asserts neither the interface nor a
metaphysical analysis of existence. -/
namespace TruthCore.Causality.ExistenceActuality

open TruthCore.German.Kant.CosmologicalInference

/-- Every represented existent at this selected world is in act in the chosen
esse respect. This OPEN interface is only one direction: it supplies neither
existence from act, actual presence of causes, causal correspondence, modal
necessity, nor identity of essence and esse. The interpretation of `InAct` and
`esse` remains that of the supplied source profile. -/
def ExistingInActAt {World Being Respect : Type} (m : Ontic World Being)
    (InAct : Being → Respect → Prop) (esse : Respect) (w : World) : Prop :=
  ∀ x, m.ExistsAt w x → InAct x esse

end TruthCore.Causality.ExistenceActuality
