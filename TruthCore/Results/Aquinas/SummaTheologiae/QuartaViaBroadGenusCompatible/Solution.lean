import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaGenus
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaBroadGenusCompatible
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics

/-- The respects of the model: `esse` (also standing for the good, the true and
the noble), a strict genus `animal`, and its differentia `rational`. -/
inductive R where
  | esse
  | animal
  | rational

/-- Model: with *genus* read broadly, the *quarta via* and Aristotle's premises
for being-not-a-genus hold together.

Two beings, `true` more than `false` in every respect, both having every
respect; `true` causes every respect in everything. `animal` is the only strict
genus, with differentia `rational`; being is said of every respect and each
respect of itself. All four *quarta via* premises, its conclusion, and
Aristotle's three premises hold, and there is a strict genus with a differentia.
So Aristotle's premises do not refute the broad genus principle. -/
theorem broadGenusReadingCompatibleWithBeingNotAGenus :
    BroadGenusReadingCompatibleWithBeingNotAGenus := by
  refine ⟨Bool, R, fun _ _ => True, fun _ x y => x = true ∧ y = false,
    fun c _ _ => c = true, fun r => r = R.animal,
    fun d g => d = R.rational ∧ g = R.animal, fun t s => t = R.esse ∨ t = s,
    R.esse, R.esse, R.esse, R.esse, ?_⟩
  -- the only maximum in any respect is `true`,
  have hMax : ∀ (r : R) (m : Bool),
      IsMaximumIn (fun (_ : Bool) (_ : R) => True)
        (fun _ x y => x = true ∧ y = false) r m → m = true := by
    intro r m hm
    cases m with
    | true => rfl
    | false => exact (hm.2 true ⟨rfl, rfl⟩).elim
  refine ⟨⟨⟨true, false, rfl, rfl⟩, ⟨true, false, rfl, rfl⟩, ⟨true, false, rfl, rfl⟩⟩,
    fun _ _ => ⟨true, trivial, fun _ hy => Bool.noConfusion hy.2⟩,
    fun _ hm => hm,
    fun r m hm _ _ _ => hMax r m hm,
    fun g hg => ⟨R.rational, rfl, hg⟩,
    fun _ _ _ _ => Or.inl rfl,
    ?_,
    ⟨R.animal, R.rational, rfl, rfl, rfl⟩,
    ⟨true, ⟨trivial, fun _ hy => Bool.noConfusion hy.2⟩, fun _ _ _ => rfl⟩⟩
  -- `animal` is not said of `rational`.
  intro g d hg hd hs
  cases hg; cases hd.1
  cases hs with
  | inl h => exact R.noConfusion h
  | inr h => exact R.noConfusion h
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaBroadGenusCompatible
