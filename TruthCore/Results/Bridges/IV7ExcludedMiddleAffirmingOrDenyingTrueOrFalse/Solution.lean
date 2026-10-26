import TruthCore.Greek.Aristotle.MetaphysicsIV7
namespace TruthCore.Results.Bridges.IV7ExcludedMiddleAffirmingOrDenyingTrueOrFalse
open TruthCore.Greek.Aristotle.Metaphysics
/-- Bridge (#401): excluded middle (`STMT-EXCLUDED-MIDDLE`) and truth by
composition, *Metaphysics* IV.7, 1011b26-27 with 1012a4-5
(`STMT-THOUGHT-TRUE-OR-FALSE-BY-COMPOSITION`), entail the second half of the
thought argument on its universal reading, 1012a2-4
(`STMT-AFFIRMING-OR-DENYING-THOUGHT-IS-TRUE-OR-FALSE`): every thought that
affirms or denies is true or false. Four cases: affirmation or denial, and its
object holding or not.

This makes exact why reading B begs the question against the intuitionist
withholder (`STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`): given composition,
excluded middle for the objects of thought is what the sourced half needs. -/
theorem affirmingOrDenyingThoughtIsTrueOrFalseOfExcludedMiddle {Thought : Type}
    (object : Thought → Prop) (Affirms Denies TrueT FalseT : Thought → Prop)
    (hExcludedMiddle : TruthCore.Logic.ExcludedMiddle)
    (hComposition : ThoughtTrueOrFalseByCompositionReading object Affirms Denies TrueT FalseT) :
    AffirmingOrDenyingThoughtIsTrueOrFalseReading Affirms Denies TrueT FalseT := by
  intro t hAffirmsOrDenies
  cases hAffirmsOrDenies with
  | inl hAffirms =>
    have hRule := (hComposition t).1 hAffirms
    cases hExcludedMiddle (object t) with
    | inl hObject =>
      -- An affirmation of what holds is true.
      exact Or.inl (hRule.1.mpr hObject)
    | inr hNotObject =>
      -- An affirmation of what does not hold is false.
      exact Or.inr (hRule.2.mpr hNotObject)
  | inr hDenies =>
    have hRule := (hComposition t).2 hDenies
    cases hExcludedMiddle (object t) with
    | inl hObject =>
      -- A denial of what holds is false.
      exact Or.inr (hRule.2.mpr hObject)
    | inr hNotObject =>
      -- A denial of what does not hold is true.
      exact Or.inl (hRule.1.mpr hNotObject)
end TruthCore.Results.Bridges.IV7ExcludedMiddleAffirmingOrDenyingTrueOrFalse
