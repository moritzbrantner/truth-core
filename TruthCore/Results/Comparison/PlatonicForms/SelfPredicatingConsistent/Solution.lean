import TruthCore.Comparison.PlatonicForms
namespace TruthCore.Results.Comparison.PlatonicForms.SelfPredicatingConsistent
open TruthCore.Greek.Plato.Forms
open TruthCore.Comparison.PlatonicForms

/-- 0 is the Form; 1 and 2 are particulars. The sole quality is admitted.
These extensions interpret predicates rather than asserting their truth of reality. -/
private def finiteModel : Vocabulary (Fin 3) Unit where
  Particular x := x ≠ 0
  Admitted _ := True
  FormOf f _ := f = 0
  Exemplifies _ _ := True
  Participates x f := x ≠ 0 ∧ f = 0
  Independent f := f = 0
  Intelligible f := f = 0
  Unchanging f := f = 0
  Explains f x _ := f = 0 ∧ x ≠ 0
  ModelFor f x := f = 0 ∧ x ≠ 0
  Imitates x f := x ≠ 0 ∧ f = 0
  Like _ _ := False
  Essentially _ _ := False

/-- Formal compatibility of precisely the scoped ten-commitment synthesis. -/
theorem selfPredicatingConsistent : SelfPredicatingConsistent := by
  refine ⟨finiteModel, ?_⟩
  constructor
  · exact ⟨1, 2, (), by decide, by decide, by decide, True.intro,
      True.intro, True.intro⟩
  · simp [OneOverMany, UniqueForms, ParticipationPredication, Nonidentity,
      OntologicalSeparation, ExplanatoryParticipation, ExemplarParticipation,
      IntelligibleForms, UniformSelfPredication, finiteModel, Ne.symm]
end TruthCore.Results.Comparison.PlatonicForms.SelfPredicatingConsistent
