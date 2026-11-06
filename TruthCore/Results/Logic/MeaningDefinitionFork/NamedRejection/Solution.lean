module

public import TruthCore.Logic.MeaningDefinitionFork
public import TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection.Solution
public import TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection.Solution

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejection
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem namedRejection {L : Language} (F : Frame L) (meaningful : L.Sentence → Prop)
    (hNotV1 : ¬ V1Definition F meaningful GlobalScope)
    (hTarget : V2ExcludedTarget F meaningful GlobalScope)
    (hClosed : MeaningClosedUnderNegation L meaningful)
    (hObservations : ∃ o₁ o₂ o₃, ChurchObservations F o₁ o₂ o₃)
    (hExcluded : ExcludedNegation meaningful) : NamedDemarcationFailure F meaningful := by
  refine ⟨hNotV1, V2Rejection.v2Rejection F meaningful GlobalScope hTarget,
    V3Rejection.v3Rejection F meaningful hClosed hObservations hExcluded, ?_⟩
  intro hAll
  obtain ⟨s, hNot⟩ := hExcluded
  exact hNot (hAll (L.neg s) True.intro)

end TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejection
