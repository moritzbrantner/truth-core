import TruthCore.German.Kant.CosmologicalInference

namespace TruthCore.Results.Kant.CosmologicalInference.ConversionNeedsExistence
open TruthCore.German.Kant.CosmologicalInference

theorem conversionNeedsExistence (m : Ontic W E) (p : RealityProfile E) (w : W)
    (hExists : NecessaryBeing m w) (hIdentify : NecessaryIsMostReal m p w)
    (hUnique : MostRealUnique p) :
    MostRealIsNecessary m p w := by
  obtain ⟨n, _, hn⟩ := hExists
  have hr : MostReal p n := hIdentify n hn
  intro x hx
  have heq : x = n := hUnique x n hx hr
  intro v hv
  rw [heq]
  exact hn v hv

end TruthCore.Results.Kant.CosmologicalInference.ConversionNeedsExistence
