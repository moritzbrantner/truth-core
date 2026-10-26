import TruthCore.Alternatives.NightCosmogony

/-!
The "potency prior" cosmogony of *Metaphysics* XII.6, 1071b22-28, as a theory
bundle (#497): the strongest sourced rival behind the bare rival
`PotencyPriorToActReading` of `ActSimplyPriorToPotencyReading`.

Its one commitment is sourced to Aristotle's report (claim
`ARIST-MET-1071B-NIGHT-GENERATION-A`); it is a theory and not the bare
contradictory of act's simple priority because it adds that the unpreceded
potency is actualized. The aporia's grounds ("whatever acts is able, but not
everything able acts", 1071b23-24) are not formalized: they constrain only
ability and act, not `PriorSimply`. Hesiod's and the Orphic theogonies
themselves are not pinned; the bundle is the position as Aristotle presents it.
-/

namespace TruthCore.Comparison.NightCosmogony

open TruthCore.Alternatives.NightCosmogony

universe u v

/-- Generation from Night: some potency that no being in act simply precedes is
reduced to act. -/
def GenerationFromNight {Being : Sort u} {Respect : Sort v}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  UnprecededPotencyActualizedReading InAct InPotency MovedIn PriorSimply

end TruthCore.Comparison.NightCosmogony

namespace TruthCore.Alternatives.NightCosmogony

universe u v

/-- Conclusion of the elimination: the Night cosmogony's bundle does not hold
(for the given interpretation of its vocabulary). Kept outside
`TruthCore.Comparison` because it is a refutation, not a theory. -/
def GenerationFromNightFalse {Being : Sort u} {Respect : Sort v}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ¬ TruthCore.Comparison.NightCosmogony.GenerationFromNight
    InAct InPotency MovedIn PriorSimply

end TruthCore.Alternatives.NightCosmogony
