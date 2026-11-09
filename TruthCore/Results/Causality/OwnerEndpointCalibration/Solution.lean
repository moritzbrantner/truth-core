module
public import TruthCore.Causality.OwnerEndpointCalibration
@[expose] public section
namespace TruthCore.Results.Causality.OwnerEndpointCalibration
open TruthCore.Causality.OwnerEndpointCalibration

theorem certificate : Certificate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W B m concrete power w h x y hxy
    exact h.2 x.val y.val hxy
  · intro W B p w x y hxy
    exact p.powerConcrete w x (p.exerciseHasPower w x y hxy)
  · intro W B R p w x y hxy
    exact (p.concreteIsEsse x).mp
      (p.powerConcrete w x (p.exerciseHasPower w x y hxy))
  · constructor
    · exact ⟨⟨fun _ h => h.elim, fun _ _ h => h.elim⟩,
        (by rintro ⟨y, h⟩; exact h), fun h => h⟩
    · constructor
      · exact ⟨⟨fun _ h => h.elim, fun _ _ h => h.elim⟩,
          True.intro, fun h => h⟩
      · exact ⟨⟨True.intro, fun h => h⟩,
          ⟨⟨fun _ h => h.elim, fun _ _ _ => True.intro⟩, True.intro⟩⟩
end TruthCore.Results.Causality.OwnerEndpointCalibration
