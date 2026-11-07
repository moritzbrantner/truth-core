module

public import TruthCore.Causality.MeinongianActuality
public import TruthCore.Results.Causality.PerfectionOfBeing.Solution

@[expose] public section

namespace TruthCore.Results.Causality.MeinongianActuality
open TruthCore.Causality.MeinongianActuality
open TruthCore.Causality.PerfectionOfBeing (PerfectOnlyInsofarAsBeing)
open TruthCore.Latin.Aquinas.SummaTheologiae (PerfectInsofarAsInActReading)

/-- Whatever is in act in a respect is perfect in it and so has being; hence
nothing is in act without being. Conditional on two OPEN premises. -/
theorem noActualityWithoutBeing {B R : Type} (PerfectIn InAct : B → R → Prop) (esse : R)
    (hPerfect : PerfectInsofarAsInActReading PerfectIn InAct)
    (hBeing : PerfectOnlyInsofarAsBeing PerfectIn InAct esse) :
    NoActualityWithoutBeing InAct esse :=
  fun ⟨x, r, hAct, hNo⟩ => hNo (hBeing x r ((hPerfect x r).mpr hAct))

open TruthCore.Causality.MeinongianActuality.Control in
theorem controls : Certificate :=
  ⟨⟨TruthCore.Results.Causality.PerfectionOfBeing.controls.2.1.1,
      TruthCore.Results.Causality.PerfectionOfBeing.controls.2.1.2.1,
      ⟨(), true, rfl, Bool.noConfusion⟩⟩,
    ⟨TruthCore.Results.Causality.PerfectionOfBeing.controls.1.1,
      TruthCore.Results.Causality.PerfectionOfBeing.controls.1.2.1,
      ⟨(), true, rfl, Bool.noConfusion⟩⟩⟩

end TruthCore.Results.Causality.MeinongianActuality
