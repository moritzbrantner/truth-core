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
def antiExplanation : Topic Bool → Topic Bool → Prop
  | .use φ, .truthConditions ψ => φ = ψ
  | .purposesOfMoralTalk, .supervenienceRequirement => True
  | _, _ => False

/-- Truth conditions explain use; the competence explanation is unchanged. -/
def realistExplanation : Topic Bool → Topic Bool → Prop
  | .truthConditions φ, .use ψ => φ = ψ
  | .purposesOfMoralTalk, .supervenienceRequirement => True
  | _, _ => False

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
  · refine ⟨?_, ?_, ?_, trivial, ?_, ?_, ?_, trivial⟩
    · intro φ _; exact rfl
    · intro h; exact h false rfl
    · intro φ _ _; exact id
    · intro φ _; exact rfl
    · intro h; exact h false rfl
    · intro φ _ h; exact h.elim

end TruthCore.Results.Comparison.QuasiRealism.SharedDataDoNotChooseOrder
