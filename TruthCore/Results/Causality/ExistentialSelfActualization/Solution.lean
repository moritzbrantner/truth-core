import TruthCore.Causality.ExistentialSelfActualization
import TruthCore.Results.Alternatives.PerSeCausalLoopImpossible.Solution

namespace TruthCore.Results.Causality.ExistentialSelfActualization
open TruthCore.Causality.ExistentialSelfActualization

/-- Register the existing mixed-token proof with exactly four named OPEN
premises, without changing its original frozen Challenge. -/
theorem noSelf {B E : Type} (Occurs : E → Prop) (bearer : E → B)
    (produces : E → B → Prop) (Prior : Sum B E → Sum B E → Prop)
    (hBearer : BearerPrior Occurs bearer Prior)
    (hProduct : ProductPrior Occurs produces Prior)
    (hIrreflexive : IrreflexivePriority Prior) (hTransitive : TransitivePriority Prior) :
    NoSelfProduction Occurs bearer produces := by
  exact TruthCore.Results.Alternatives.PerSeCausalLoopImpossible.noExistentialSelfActualization
    Occurs bearer produces Prior hBearer hProduct hIrreflexive hTransitive

/-- Register the same existing omission and positive interpretations. -/
theorem controls : Controls := by
  exact ⟨TruthCore.Results.Alternatives.PerSeCausalLoopImpossible.existentialSelfActualizationNeedsTransitivity,
    TruthCore.Results.Alternatives.PerSeCausalLoopImpossible.existentialSelfActualizationNeedsIrreflexivity,
    TruthCore.Results.Alternatives.PerSeCausalLoopImpossible.otherBearerCanActualizeExistence⟩

end TruthCore.Results.Causality.ExistentialSelfActualization
