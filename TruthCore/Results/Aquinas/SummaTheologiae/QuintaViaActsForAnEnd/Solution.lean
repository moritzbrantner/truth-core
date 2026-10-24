import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuintaVia
import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaActsForAnEnd
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

/-- ST I q.2 a.3 co., fifth way, first half: natural bodies regularly attain what
is best; what is regular is not by chance; what regularly attains the best does
so by chance or from intention. So each natural body tends to something best for
it, not by chance. -/
theorem actsForAnEnd {Being : Type} {End : Type}
    (NaturalBody : Being → Prop)
    (RegularlyAttains Best ByChance TendsTo : Being → End → Prop)
    (hObs : NaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best)
    (hNotChance : RegularityIsNotByChanceReading RegularlyAttains ByChance)
    (hDich : RegularBestByChanceOrByIntentionReading RegularlyAttains Best ByChance TendsTo) :
    NaturalBodiesActForAnEndNotByChanceReading NaturalBody Best ByChance TendsTo := by
  intro x hx
  -- INF-AQUINAS-ST-I-Q2-A3-QUINTA-VIA-ACTS-FOR-AN-END: x regularly attains a best e,
  obtain ⟨e, hReg, hBest⟩ := hObs.2 x hx
  -- not by chance,
  have hNC : ¬ ByChance x e := hNotChance x e hReg
  -- so, by the dichotomy, from intention
  cases hDich x e hReg hBest with
  | inl hChance => exact absurd hChance hNC
  | inr hTends => exact ⟨e, hBest, hNC, hTends⟩

/-- The dichotomy is needed (necessity or selection model): bodies regularly attain
the best and not by chance, but tend to nothing. -/
theorem necessityModel :
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    ¬ RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd noEnd ∧
    ¬ NaturalBodiesActForAnEndNotByChanceReading isBody allEnd noEnd noEnd := by
  refine ⟨⟨⟨.b0, trivial⟩, fun _ hx => ⟨(), hx, trivial⟩⟩, fun _ _ _ h => h, ?_, ?_⟩
  · intro h
    cases h .b0 () trivial trivial with
    | inl h => exact h
    | inr h => exact h
  · intro h
    obtain ⟨_, _, _, h⟩ := h .b0 trivial
    exact h

/-- The no-chance premise is needed (chance model): bodies regularly attain the
best, but by chance. -/
theorem chanceModel :
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd allEnd noEnd ∧
    ¬ RegularityIsNotByChanceReading bodyEnd allEnd ∧
    ¬ NaturalBodiesActForAnEndNotByChanceReading isBody allEnd allEnd noEnd := by
  refine ⟨⟨⟨.b0, trivial⟩, fun _ hx => ⟨(), hx, trivial⟩⟩, fun _ _ _ _ => Or.inl trivial,
    ?_, ?_⟩
  · intro h
    exact h .b0 () trivial trivial
  · intro h
    obtain ⟨_, _, hNC, _⟩ := h .b0 trivial
    exact hNC trivial
end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaActsForAnEnd
