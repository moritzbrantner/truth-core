import TruthCore.Ontology.NaturalismLaws
namespace TruthCore.Results.Ontology.NaturalismLaws.Instantiation
open TruthCore.Ontology.NaturalismLaws TruthCore.Ontology.Naturalism
open TruthCore.Ontology.Spatiotemporal

theorem instantiated {W B R : Type} (m : Representation W B R) (w : W)
    (h : ExistenceNaturalism (ontic m) (Located (frame m (immanentAt m w))) w) :
    ExistingLawsInstantiated m w := by
  sorry

theorem excludesUninstantiated {W B R : Type} (m : Representation W B R) (w : W)
    (h : ExistenceNaturalism (ontic m) (Located (frame m (immanentAt m w))) w) :
    ¬ ∃ l, m.lawPresent w l ∧ ¬ ActualInstance m w l := by
  sorry
end TruthCore.Results.Ontology.NaturalismLaws.Instantiation
