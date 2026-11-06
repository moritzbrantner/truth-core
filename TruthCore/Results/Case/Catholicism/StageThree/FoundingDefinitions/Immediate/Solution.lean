module

public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Immediate

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Frozen semantic-comparison obligation; no preferred reading is adopted. -/
theorem immediateCalibration (σ : Signature) (A : Agency σ) (direct : σ.Being → σ.Society → Prop)
    (hImmediate : ImmediateOnlyReading σ A direct) :
    ImmediateEnvoyCalibration σ A direct := by
  constructor
  · intro hEnvoy g c hGod hEvent
    exact (hImmediate g c hGod).1 (hEnvoy g c hGod hEvent.1 hEvent.2)
  · intro hAdmits g c hGod hFounded hTeach
    exact (hImmediate g c hGod).2 (hAdmits g c hGod ⟨hFounded, hTeach⟩)

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Immediate
