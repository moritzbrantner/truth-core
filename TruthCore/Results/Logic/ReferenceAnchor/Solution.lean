module

public import TruthCore.Logic.ReferenceAnchor

@[expose] public section
namespace TruthCore.Results.Logic.ReferenceAnchor
open TruthCore.Logic.ReferenceAnchor
open TruthCore.Modern.Russell.Existence

theorem checks : ReferenceBoundary := by
  have sentences : SameSentences := by
    intro φ
    exact @FirstOrder.Language.StrongHomClass.realize_sentence language Bool Bool
      original transported _ _ _ (@Equiv.inducedStructureEquiv language Bool Bool original swap) φ
  refine ⟨sentences, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Γ φ
    constructor
    · intro h premises
      exact (sentences φ).mp (h (fun ψ hψ => (sentences ψ).mpr (premises ψ hψ)))
    · intro h premises
      exact (sentences φ).mpr (h (fun ψ hψ => (sentences ψ).mp (premises ψ hψ)))
  · decide
  · exact ⟨false, fun _ => Iff.rfl⟩
  · rfl
  · change ¬ (true = false)
    decide
  · intro E F a b description ha hb
    exact ((TruthCore.Results.Modern.Russell.Description.checks E F).mp description).2 a b ha hb

end TruthCore.Results.Logic.ReferenceAnchor
