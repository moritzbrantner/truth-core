module

public import TruthCore.Causality.MaximumDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.MaximumDefinitions.CausalTransport
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.MaximumDefinitionFork

/-- Frozen analyst interface; no real-world degree interpretation is adopted. -/
theorem causalTransport {Degree : Type} [Preorder Degree] (f : Frame Degree)
    (hBridge : MaximalToGreatest f)
    (hSource : GreatestDegreeCausesAllInGenusReading f.InAct f.CausesIn f.selected f.value) :
    MaximumInBeingCausesAllBeingsReading f.InAct f.MoreIn f.CausesIn f.selected := by
  intro m hm
  exact hSource m (hBridge m hm)

end TruthCore.Results.Causality.MaximumDefinitions.CausalTransport
