module

public import TruthCore.Causality.SpineWalkFrame

@[expose] public section

namespace TruthCore.Results.Causality.SpineWalkFrame
open TruthCore.Causality.SpineWalkFrame
open TruthCore.Causality.SpineRivalsStageOne
open TruthCore.German.Kant.CosmologicalInference (Ontic)

/-- Price of the rival of actual reflexivity under the Euclidean premise: the
selected world is the only world in view that does not access itself. -/
theorem rivalIsolatesActual {W B : Type} (m : Ontic W B) (w : W)
    (hEuclidean : TruthCore.Modal.Euclidean m.frame)
    (hRival : ActualIrreflexiveSerial m w) :
    ActualAloneNotSelfAccessible m w :=
  ⟨hRival.1, hRival.2 w, fun v hv => hEuclidean w v v hv hv⟩

end TruthCore.Results.Causality.SpineWalkFrame
