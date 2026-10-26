import TruthCore.Comparison.Stevenson
import TruthCore.Results.Comparison.Metaethics.StevensonEmotivismConsistent.Solution

namespace TruthCore.Results.Comparison.Metaethics.StevensonFactualAgreement
open TruthCore.Comparison.Stevenson
open TruthCore.English.Stevenson

/-- Reuse the existing two-agent comparison interpretation. Clash is refined
from an unconstrained primitive to opposed interests with mutual redirection.
Both agents believe the sole designated factual sentence. -/
def model : Sig where
  toSig := { StevensonEmotivismConsistent.model with
    ClashInAttitude := fun x y _ => x = true ∧ y = false }
  Factual := fun _ => True
  Favors := fun x _ => x = true
  Disfavors := fun x _ => x = false
  Believes := fun _ _ => True
  SeeksChange := fun x y _ => (x = true ∧ y = false) ∨ (x = false ∧ y = true)

theorem factualAgreementConsistent : FactualAgreementConsistent := by
  refine ⟨model, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ => ⟨(), trivial⟩
  · exact fun _ _ => trivial
  · exact fun _ _ _ hx hy => ⟨hx, hy⟩
  · constructor
    · intro x y p
      constructor
      · intro h
        exact ⟨h.1, h.2, Or.inl h, Or.inr ⟨h.2, h.1⟩⟩
      · intro h
        exact ⟨h.1, h.2.1⟩
    · exact ⟨true, false, (), trivial, ⟨rfl, rfl⟩,
        (fun _ _ => Iff.rfl), ⟨(), trivial⟩⟩
end TruthCore.Results.Comparison.Metaethics.StevensonFactualAgreement
