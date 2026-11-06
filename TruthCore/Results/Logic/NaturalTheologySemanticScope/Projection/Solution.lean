module

public import TruthCore.Logic.NaturalTheologySemanticScope

@[expose] public section
namespace TruthCore.Results.Logic.NaturalTheologySemanticScope.Projection
open TruthCore.Logic.Verificationism
open TruthCore.Logic.NaturalTheologySemanticScope
open TruthCore.Logic.NaturalTheologySemanticScope.Control
open TruthCore.Results.Logic.Verificationism.VerdictSilent
theorem projection {L : Language} (F : Frame L) (p : Profile L)
    (h : NoMeaningfulDivine p) : NotNaturalTheologyArguable F p := by
  intro ⟨s, hMeaningful, hAboutGod, _⟩
  exact (h s hMeaningful).1 hAboutGod
end TruthCore.Results.Logic.NaturalTheologySemanticScope.Projection
