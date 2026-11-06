module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.Controls
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork

/-- Frozen analyst obligation; no source communication is reinterpreted silently. -/
theorem controls : Controls := by
  have hs : SameSenseTransfer sameSense := by
    intro s h e hu hc he
    exact rfl
  have hd : EsseReceivedOnlyInOwnEssence differentSense.essenceOf
      (differentSense.Received differentSense.selected) := by
    intro x r h; exact False.elim h
  refine ⟨⟨True.intro, ?_, rfl, hs, Bool.noConfusion, rfl, ?_, ?_⟩,
    ⟨True.intro, ?_, rfl, Bool.noConfusion, ?_, ?_, hd⟩,
    ⟨True.intro, ?_, ?_, Bool.noConfusion, ?_⟩,
    ⟨?_, rfl, ?_, ?_, ?_⟩,
    ⟨True.intro, rfl, ?_, ?_, ?_⟩,
    rfl, ?_, ?_⟩
  · intro _; exact rfl
  · intro h; exact Bool.noConfusion (h false true rfl)
  · intro x r he _; exact False.elim he
  · intro _; exact rfl
  · intro h; exact h
  · exact ⟨(), true, false, True.intro, rfl, rfl, fun h => h⟩
  · intro _; exact rfl
  · intro s h e hu hc he
    exact False.elim (Bool.noConfusion (hc.symm.trans he))
  · intro h; exact h
  · intro h; exact False.elim h
  · intro s h e hu hc he; exact False.elim hu
  · intro h; exact h
  · intro h; exact h
  · intro s h e hu hc he; exact False.elim hc
  · intro h; exact h True.intro
  · intro h; exact h
  · intro x r hr; exact hr
  · intro h; exact h rfl

end TruthCore.Results.Causality.EsseReceptionDefinitions.Controls
