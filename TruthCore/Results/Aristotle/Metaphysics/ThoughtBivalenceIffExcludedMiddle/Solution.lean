import TruthCore.Greek.Aristotle.MetaphysicsIV7
import TruthCore.Results.Aristotle.Metaphysics.TruthAptThoughtDecidesItsObject.Solution
namespace TruthCore.Results.Aristotle.Metaphysics.ThoughtBivalenceIffExcludedMiddle
open TruthCore.Logic
open TruthCore.Greek.Aristotle.Metaphysics
/-- *Metaphysics* IV.7, 1012a2-5, reading B: given that thought that is true or false
affirms or denies, that thought is true or false by composition, and that every
proposition can be affirmed or denied in thought, the universal premise "every
object of thought is judged truly or falsely" holds exactly when excluded
middle does. Constructive in both directions. So reading B is not an argument
*for* excluded middle that the intuitionist must answer separately: its premise
is excluded middle restated for thought, and withholding the one is withholding
the other. -/
theorem thoughtBivalenceIffExcludedMiddle {Thought : Type}
    (object : Thought → Prop) (Affirms Denies TrueT FalseT : Thought → Prop)
    (hDefinition : TruthAptThoughtAffirmsOrDeniesReading Affirms Denies TrueT FalseT)
    (hComposition : ThoughtTrueOrFalseByCompositionReading object Affirms Denies TrueT FalseT)
    (hEvery : ThoughtAffirmsOrDeniesEveryPropositionReading object Affirms Denies) :
    ThoughtBivalenceIffExcludedMiddle object TrueT FalseT := by
  -- Reading A (result ARIST-MET-1012A-TRUTH-APT-THOUGHT-DECIDES-ITS-OBJECT).
  have hDecides := TruthAptThoughtDecidesItsObject.truthAptThoughtDecidesItsObject
    object Affirms Denies TrueT FalseT hDefinition hComposition
  constructor
  · -- Bivalence of thought gives excluded middle.
    intro hBivalence p
    obtain ⟨t, hIs, hApt⟩ := hBivalence p
    cases hDecides t hApt with
    | inl hObject => exact Or.inl (hIs.mp hObject)
    | inr hNotObject => exact Or.inr (fun hp => hNotObject (hIs.mpr hp))
  · -- Excluded middle gives bivalence of thought: the thought about p is true
    -- or false according to whether p holds and whether it affirms or denies.
    intro hExcludedMiddle p
    obtain ⟨t, hIs, hAct⟩ := hEvery p
    refine ⟨t, hIs, ?_⟩
    cases hAct with
    | inl hAffirms =>
      have hRule := (hComposition t).1 hAffirms
      cases hExcludedMiddle p with
      | inl hp => exact Or.inl (hRule.1.mpr (hIs.mpr hp))
      | inr hnp => exact Or.inr (hRule.2.mpr (fun hObject => hnp (hIs.mp hObject)))
    | inr hDenies =>
      have hRule := (hComposition t).2 hDenies
      cases hExcludedMiddle p with
      | inl hp => exact Or.inr (hRule.2.mpr (hIs.mpr hp))
      | inr hnp => exact Or.inl (hRule.1.mpr (fun hObject => hnp (hIs.mp hObject)))
end TruthCore.Results.Aristotle.Metaphysics.ThoughtBivalenceIffExcludedMiddle
