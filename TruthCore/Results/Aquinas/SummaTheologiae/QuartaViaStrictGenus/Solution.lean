import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaGenus
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaStrictGenus
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics

/-- The respects of the model: `esse` (also standing for the good, the true and
the noble), a strict genus `animal`, and its differentia `rational`. -/
inductive R where
  | esse
  | animal
  | rational

/-- Countermodel: with *genus* read strictly, the *quarta via* fails at being.

Two beings, `true` more than `false` in every respect, both having every
respect. `animal` is the only strict genus, with differentia `rational`; being
is said of every respect and each respect of itself. The maximum `true` causes
only in the genus `animal`. Every premise holds: the strict genus principle is
satisfied (the maximum causes all in `animal`), and Aristotle's premises make
being no genus. Yet the maximum in being causes nothing's being. -/
theorem strictGenusReadingDoesNotYieldQuartaVia :
    StrictGenusReadingDoesNotYieldQuartaVia := by
  intro h
  obtain ⟨m, _, hCauses⟩ := h Bool R (fun _ _ => True)
    (fun _ x y => x = true ∧ y = false) (fun _ _ r => r = R.animal)
    (fun r => r = R.animal) (fun d g => d = R.rational ∧ g = R.animal)
    (fun t s => t = R.esse ∨ t = s) R.esse R.esse R.esse R.esse
    -- grades are found in things,
    ⟨⟨true, false, rfl, rfl⟩, ⟨true, false, rfl, rfl⟩, ⟨true, false, rfl, rfl⟩⟩
    -- every gradation has the maximum `true`,
    (fun _ _ => ⟨true, trivial, fun _ hy => Bool.noConfusion hy.2⟩)
    -- the maximally true is maximally being (one respect),
    (fun _ hm => hm)
    -- the strict genus principle holds: at `animal` the maximum causes all,
    (fun r hr _ _ _ _ _ => hr)
    -- `animal` has the differentia `rational`,
    (fun g hg => ⟨R.rational, rfl, hg⟩)
    -- being is said of every differentia,
    (fun _ _ _ _ => Or.inl rfl)
    -- and `animal` is not said of `rational`.
    (fun g d hg hd hs => by
      cases hg; cases hd.1
      cases hs with
      | inl h => exact R.noConfusion h
      | inr h => exact R.noConfusion h)
  -- The maximum's other being has esse, but is not caused in esse.
  cases m with
  | true => exact R.noConfusion (hCauses false Bool.noConfusion trivial)
  | false => exact R.noConfusion (hCauses true Bool.noConfusion trivial)
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaStrictGenus
