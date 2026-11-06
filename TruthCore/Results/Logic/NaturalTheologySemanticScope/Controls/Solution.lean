module

public import TruthCore.Logic.NaturalTheologySemanticScope

@[expose] public section
namespace TruthCore.Results.Logic.NaturalTheologySemanticScope.Controls
open TruthCore.Logic.Verificationism
open TruthCore.Logic.NaturalTheologySemanticScope
open TruthCore.Logic.NaturalTheologySemanticScope.Control
open TruthCore.Results.Logic.Verificationism.VerdictSilent
theorem controls : Control.Properties := by
  have formal : Meets observableFrame profile .consequence () := by
    intro w hw
    exact hw divine (List.Mem.head [])
  refine ⟨True.intro, True.intro, ?_, True.intro, rfl, formal,
    (fun h => h), (fun h => h), ?_, ?_⟩
  · intro h
    exact (h divine True.intro).1 True.intro
  · intro ⟨s, _, _, a, _, hWorld, _, _⟩
    cases a
    exact hWorld divine (List.Mem.head [])
  · intro h
    exact h () True.intro formal
end TruthCore.Results.Logic.NaturalTheologySemanticScope.Controls
