module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.ReceptionTransfer
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork

/-- Frozen analyst obligation; no source communication is reinterpreted silently. -/
theorem receptionTransfer (f : Frame) (hUnion : SelectedUnion f)
    (hCommunication : UnitedCommunication f) (hAct : CommunicatedActIsSoulEsse f)
    (hTransfer : SameSenseTransfer f) : SelectedReception f := by
  exact hTransfer f.selected f.human f.communicatedAct hUnion (hCommunication hUnion) hAct

end TruthCore.Results.Causality.EsseReceptionDefinitions.ReceptionTransfer
