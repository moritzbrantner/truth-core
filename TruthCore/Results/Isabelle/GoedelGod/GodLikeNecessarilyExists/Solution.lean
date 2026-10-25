import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Isabelle.GoedelGod.GodLikeNecessarilyExists
open TruthCore.Modal (Frame Symmetric)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Isabelle.AFP.GoedelGod

/-- AFP `T1` (`by (metis A1a A2)`): positive properties are possibly
exemplified. If a positive `Φ` were not possibly exemplified, `Φ` would
necessarily imply its own negation, so by `A2` the negation would be positive,
and by `A1a` `Φ` would not be. Excluded middle decides whether `Φ` is possibly
exemplified. -/
theorem positivePossiblyExemplified {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hA1a : NegationPositiveExcludesPositive P)
    (hA2 : PositiveClosedUnderNecessaryImplication F P)
    (hEM : ExcludedMiddle) :
    PositivePossiblyExemplified F P := by
  intro w Φ hPos
  cases hEM (Dia F (fun v => ∃ x, Φ x v) w) with
  | inl hPossible => exact hPossible
  | inr hNotPossible =>
    have hImpliesNeg : Box F (fun v => ∀ x, Φ x v → ¬ Φ x v) w :=
      fun v hAccess x hx _ => hNotPossible ⟨v, hAccess, x, hx⟩
    exact absurd hPos (hA1a w Φ (hA2 w Φ (fun x v => ¬ Φ x v) hPos hImpliesNeg))

/-- AFP corollary `C` (`by (metis A3 T1)`): being God-like is positive (`A3`),
so by `T1` a God-like being possibly exists. -/
theorem godLikePossiblyExists {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hT1 : PositivePossiblyExemplified F P)
    (hA3 : GodLikePositive P) :
    GodLikePossiblyExists F P :=
  fun w => hT1 w (GodLike P) (hA3 w)

/-- AFP `T2` (`by (metis A1b A4 G_def ess_def)`): being God-like is an essence
of every God-like being. Let `x` be God-like and have `Ψ`. `Ψ` is positive:
otherwise its negation would be positive (`A1b`), and `x`, having every
positive property, would lack `Ψ`. A positive property is necessarily positive
(`A4`), so at every accessible world every God-like being has `Ψ`. Excluded
middle decides whether `Ψ` is positive. -/
theorem godLikeIsEssence {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hA1b : NonPositiveHasPositiveNegation P)
    (hA4 : PositiveNecessarilyPositive F P)
    (hEM : ExcludedMiddle) :
    GodLikeIsEssence F P := by
  intro w x hGodLike
  refine ⟨hGodLike, ?_⟩
  intro Ψ hΨ
  cases hEM (P Ψ w) with
  | inl hPos =>
    intro v hAccess y hGodLikeY
    exact hGodLikeY Ψ (hA4 w Ψ hPos v hAccess)
  | inr hNotPos =>
    exact absurd hΨ (hGodLike (fun z u => ¬ Ψ z u) (hA1b w Ψ hNotPos))

/-- A God-like being at a world exists necessarily there: necessary existence
is positive (`A5`) and the God-like being has every positive property. -/
theorem godLikeNecessarilyExistsAt {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hA5 : NecessaryExistencePositive F P)
    {u : World} {x : Ind} (hGodLike : GodLike P x u) :
    NecessaryExistence F x u :=
  hGodLike (NecessaryExistence F) (hA5 u)

/-- AFP `T3` (`by (metis A5 C T2 sym G_def NE_def)`). Take any world `w` and
any `v` accessible from it. By `C` at `v`, some `u` accessible from `v` has a
God-like `x`. By `T2` being God-like is an essence of `x` at `u`, and `x`
exists necessarily at `u` (`A5`), so at every world accessible from `u` a
God-like being exists. By symmetry `v` is accessible from `u`, so a God-like
being exists at `v`. -/
theorem godLikeNecessarilyExists {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hA1a : NegationPositiveExcludesPositive P)
    (hA1b : NonPositiveHasPositiveNegation P)
    (hA2 : PositiveClosedUnderNecessaryImplication F P)
    (hA3 : GodLikePositive P)
    (hA4 : PositiveNecessarilyPositive F P)
    (hA5 : NecessaryExistencePositive F P)
    (hSym : Symmetric F)
    (hEM : ExcludedMiddle) :
    GodLikeNecessarilyExists F P := by
  have hT1 := positivePossiblyExemplified F P hA1a hA2 hEM
  have hC := godLikePossiblyExists F P hT1 hA3
  have hT2 := godLikeIsEssence F P hA1b hA4 hEM
  intro w v _hWV
  obtain ⟨u, hVU, x, hGodLike⟩ := hC v
  exact godLikeNecessarilyExistsAt F P hA5 hGodLike (GodLike P) (hT2 u x hGodLike)
    v (hSym v u hVU)

/-- One world, one individual, every world accessing every world, and a
property positive exactly when the one individual has it. Every axiom then
reduces to a tautology about that individual. -/
theorem premisesJointlySatisfiable :
    ∃ (World Ind : Type) (F : Frame World) (P : Positivity World Ind),
      NegationPositiveExcludesPositive P ∧
      NonPositiveHasPositiveNegation P ∧
      PositiveClosedUnderNecessaryImplication F P ∧
      GodLikePositive P ∧
      PositiveNecessarilyPositive F P ∧
      NecessaryExistencePositive F P ∧
      Symmetric F := by
  refine ⟨Unit, Unit, ⟨fun _ _ => True⟩, fun Φ w => Φ () w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hNeg hPos
    exact hNeg hPos
  · intro w Φ hNotPos
    exact hNotPos
  · intro w Φ Ψ hPos hBox
    exact hBox w trivial () hPos
  · intro w Φ hPos
    exact hPos
  · intro w Φ hPos v _
    cases v
    cases w
    exact hPos
  · intro w Φ hEssence v _
    cases v
    cases w
    exact ⟨(), hEssence.1⟩
  · intro _ _ _
    trivial
end TruthCore.Results.Isabelle.GoedelGod.GodLikeNecessarilyExists
