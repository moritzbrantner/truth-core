module

public import TruthCore.Ontology.NaturalismLaws

@[expose] public section
namespace TruthCore.Results.Ontology.NaturalismLaws.Instantiation
open TruthCore.Ontology.NaturalismLaws TruthCore.Ontology.Naturalism
open TruthCore.Ontology.Spatiotemporal

theorem instantiated {W B R : Type} (m : Representation W B R) (w : W)
    (h : ExistenceNaturalism (ontic m) (Located (frame m (immanentAt m w))) w) :
    ExistingLawsInstantiated m w := by
  intro l hl
  obtain ⟨r, b, hb, hi, _⟩ := h (.inr l) hl
  exact ⟨b, hb, hi⟩

theorem excludesUninstantiated {W B R : Type} (m : Representation W B R) (w : W)
    (h : ExistenceNaturalism (ontic m) (Located (frame m (immanentAt m w))) w) :
    ¬ ∃ l, m.lawPresent w l ∧ ¬ ActualInstance m w l := by
  intro ⟨l, hl, hn⟩
  exact hn (instantiated m w h l hl)
end TruthCore.Results.Ontology.NaturalismLaws.Instantiation
