import TruthCore.Modern.Russell.Existence
namespace TruthCore.Results.Modern.Russell.Grounding
open TruthCore.Modern.Russell.Existence
private theorem emptyAsymmetric : Asymmetric emptyGround := by
  intro p q h
  exact h.elim
private theorem linkedAsymmetric : Asymmetric linkedGround := by
  rintro p q ⟨hp, hq⟩ ⟨hqp, _⟩
  cases hp
  cases hq
  exact Fact.noConfusion hqp
private theorem emptySound : Sound singleA emptyGround := by
  intro p q h
  exact h.elim
private theorem linkedSound : Sound singleA linkedGround := by
  rintro p q ⟨hp, hq⟩
  cases hp
  cases hq
  exact ⟨trivial, rfl⟩
theorem checks : GroundingBoundary := by
  refine ⟨⟨.a, rfl⟩, emptyAsymmetric, linkedAsymmetric,
    emptySound, linkedSound, ⟨rfl, rfl⟩, (fun h => h), ?_⟩
  intro h
  exact (h linkedGround emptyGround linkedAsymmetric emptyAsymmetric
    linkedSound emptySound (.basis .a) (.instance .a)).mp ⟨rfl, rfl⟩
end TruthCore.Results.Modern.Russell.Grounding
