module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary
public import TruthCore.Case.Catholicism.StageThree.CommissionAttestation

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionAttestation
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem governingComponentsDoNotForceTeachingScope : GoverningComponentsDoNotForceTeachingScope := by
  constructor
  · refine ⟨modelSig True, modelAgency True (fun p => p) True True False,
      fullCommissioning, ?_, ?_, ⟨true, trivial, trivial, trivial⟩, ?_⟩
    · intro _ _ _ _ _; trivial
    · exact ⟨fun _ _ => trivial, Or.inl (fun _ _ => trivial)⟩
    · intro h; exact (h true trivial trivial trivial).2
  · let E : Commissioning := ⟨fun p => p = .keys⟩
    refine ⟨modelSig True, modelAgency True (fun p => p) True True False,
      E, ?_, ⟨.keys, rfl, rfl⟩, ⟨true, trivial, trivial, trivial⟩, ?_⟩
    · intro _ _ _ _
      refine ⟨fun _ _ _ => trivial, ?_⟩
      intro hg
      cases hg
    · intro h; exact (h true trivial trivial trivial).2

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
