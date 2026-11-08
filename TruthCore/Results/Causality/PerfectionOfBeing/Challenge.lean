import TruthCore.Causality.PerfectionOfBeing

namespace TruthCore.Results.Causality.PerfectionOfBeing
open TruthCore.Causality.PerfectionOfBeing
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- In act in a respect, so perfect in it, so having being. Conditional on two
OPEN premises. -/
theorem actualityOnlyInsofarAsBeing {B R : Type} (PerfectIn InAct : B → R → Prop) (esse : R)
    (hPerfect : PerfectInsofarAsInActReading PerfectIn InAct)
    (hBeing : PerfectOnlyInsofarAsBeing PerfectIn InAct esse) :
    ActualityOnlyInsofarAsBeingReading InAct esse := by
  sorry

theorem controls : TruthCore.Causality.PerfectionOfBeing.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.PerfectionOfBeing
