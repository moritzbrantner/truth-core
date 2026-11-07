import TruthCore.Causality.MeinongianActuality

namespace TruthCore.Results.Causality.MeinongianActuality
open TruthCore.Causality.MeinongianActuality
open TruthCore.Causality.PerfectionOfBeing (PerfectOnlyInsofarAsBeing)
open TruthCore.Latin.Aquinas.SummaTheologiae (PerfectInsofarAsInActReading)

/-- Whatever is in act in a respect is perfect in it and so has being; hence
nothing is in act without being. Conditional on two OPEN premises. -/
theorem noActualityWithoutBeing {B R : Type} (PerfectIn InAct : B → R → Prop) (esse : R)
    (hPerfect : PerfectInsofarAsInActReading PerfectIn InAct)
    (hBeing : PerfectOnlyInsofarAsBeing PerfectIn InAct esse) :
    NoActualityWithoutBeing InAct esse := by
  sorry

theorem controls : TruthCore.Causality.MeinongianActuality.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.MeinongianActuality
