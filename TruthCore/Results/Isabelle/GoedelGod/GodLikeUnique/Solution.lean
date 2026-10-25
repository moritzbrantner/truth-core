import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Isabelle.GoedelGod.GodLikeUnique
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Isabelle.AFP.GoedelGod

/-- AFP `Flawlessness` (`by (metis A1b G_def)`): a God-like being has no
property that is not positive. If `Φ` is not positive, its negation is
(`A1b`), and the God-like being has every positive property. -/
theorem godLikeFlawless {World : Type} {Ind : Type}
    (P : Positivity World Ind)
    (hA1b : NonPositiveHasPositiveNegation P) :
    GodLikeFlawless P :=
  fun w Φ _x hGodLike hNotPos => hGodLike (fun z u => ¬ Φ z u) (hA1b w Φ hNotPos)

/-- AFP `Monotheism` (`by (metis Flawlessness G_def)`). Let `x` and `y` be
God-like at `w`, and let `x` have `Φ` there. If `Φ` is positive, `y` has it,
being God-like. If not, `x` would lack it by flawlessness. Excluded middle
decides whether `Φ` is positive. -/
theorem godLikeUnique {World : Type} {Ind : Type}
    (P : Positivity World Ind)
    (hA1b : NonPositiveHasPositiveNegation P)
    (hEM : ExcludedMiddle) :
    GodLikeUnique P := by
  intro w x y hX hY Φ hΦ
  cases hEM (P Φ w) with
  | inl hPos => exact hY Φ hPos
  | inr hNotPos => exact absurd hΦ (godLikeFlawless P hA1b w Φ x hX hNotPos)
end TruthCore.Results.Isabelle.GoedelGod.GodLikeUnique
