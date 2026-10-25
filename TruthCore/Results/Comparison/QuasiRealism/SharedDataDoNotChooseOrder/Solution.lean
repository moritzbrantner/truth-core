import TruthCore.Metaethics.ExplanationOrder
import TruthCore.Results.Comparison.MoralError.AquinasGermansErred.Solution
namespace TruthCore.Results.Comparison.QuasiRealism.SharedDataDoNotChooseOrder
open TruthCore.Metaethics.ExplanationOrder

/-- `false` is the robbery judgment; `true` the evil-exists sentence. A second
agent varies acceptance with the practice while the Germans' error persists.
No claim that these two source examples name the same historical corruption. -/
def testData : Data where
  Practice := Bool
  Agent := Bool
  Sentence := Bool
  Matter := Unit
  Being := Unit
  Perfection := Unit
  Moral := fun φ => φ = false
  TruthApt := fun _ => True
  Holds := fun _ φ => φ = true
  Accepts := fun p x φ => (x = false ∧ φ = false) ∨ (x = true ∧ p = true)
  BelievesGood := fun x _ => x = false
  NaturallyEvil := fun _ => True
  NeedsCorrection := fun x _ => x = false
  germans := false
  robberyNotUnjust := false
  Due := fun _ _ => True
  Has := fun _ _ => False
  Evil := fun _ => True
  evilPremise := true

/-- Semantic use explains truth conditions; purposes explain competence. -/
def antiExplanation (x y : Topic Bool) : Prop :=
  (∃ φ, x = .use φ ∧ y = .truthConditions φ) ∨
    (x = .purposesOfMoralTalk ∧ y = .supervenienceRequirement)

/-- Truth conditions explain use; the competence explanation is unchanged. -/
def realistExplanation (x y : Topic Bool) : Prop :=
  (∃ φ, x = .truthConditions φ ∧ y = .use φ) ∨
    (x = .purposesOfMoralTalk ∧ y = .supervenienceRequirement)

/-- Both models literally share all non-explanatory data. -/
theorem testDataSatisfiesSharedData : SharedData testData := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ _; trivial
  · intro p; exact ⟨Or.inl ⟨rfl, rfl⟩, rfl, Bool.noConfusion⟩
  · exact ⟨false, (), rfl, trivial, rfl⟩
  · intro x; exact ⟨fun _ => ⟨(), trivial, id⟩, fun _ => trivial⟩
  · exact ⟨(), (), trivial, id⟩
  · intro p _; rfl
  · refine ⟨true, false, true, true, Or.inr ⟨rfl, rfl⟩, ?_⟩
    intro h
    cases h with
    | inl h => exact Bool.noConfusion h.1
    | inr h => exact Bool.noConfusion h.2
  · intro p q; exact Iff.rfl

/-- Compose the already checked moral-error theorem; derive the evil premise
from a privation, independently of the explanation relation. -/
theorem sharedDataDoNotChooseOrder : SharedDataDoNotChooseOrder := by
  have hData := testDataSatisfiesSharedData
  refine ⟨testData, hData, ?_, ?_, antiExplanation, realistExplanation, ?_⟩
  · intro p
    exact TruthCore.Results.Comparison.MoralError.AquinasGermansErred.aquinasGermansErred
      (testData.Accepts p) testData.Moral testData.TruthApt (testData.Holds p)
      testData.germans testData.robberyNotUnjust hData.1 (hData.2.1 p)
  · obtain ⟨_, _, _, hPrivation, ⟨x, g, hDue, hLacks⟩, hTruth, _⟩ := hData
    intro p
    exact hTruth p ⟨x, (hPrivation x).mpr ⟨g, hDue, hLacks⟩⟩
  · refine ⟨?_, ?_, ?_, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
    · intro φ _; exact Or.inl ⟨φ, rfl, rfl⟩
    · intro h
      rcases h false rfl with ⟨φ, hEq, _⟩ | ⟨hEq, _⟩
      · cases hEq
      · cases hEq
    · intro φ _ _ h
      rcases h with ⟨ψ, hEq, _⟩ | ⟨hEq, _⟩
      · cases hEq
      · cases hEq
    · intro φ _; exact Or.inl ⟨φ, rfl, rfl⟩
    · intro h
      rcases h false rfl with ⟨φ, hEq, _⟩ | ⟨hEq, _⟩
      · cases hEq
      · cases hEq
    · intro φ _ h
      rcases h with ⟨ψ, hEq, _⟩ | ⟨hEq, _⟩
      · cases hEq
      · cases hEq

end TruthCore.Results.Comparison.QuasiRealism.SharedDataDoNotChooseOrder
