module

public import Mathlib.Order.Directed
public import Mathlib.Order.Zorn
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Models.QuartaViaCausalAscent

/-! The *quarta via*'s grades-to-maximum step (`STMT-GRADES-HAVE-A-MAXIMUM`)
derived by causal ascent (#341), with one omission countermodel per nonlogical
premise, and two order-theoretic facts on the homogeneous-scale reading: a
Zorn form of the existence step and directedness turning a maximal grade into
a greatest one. -/

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaGradesFromCausalAscent
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Models.QuartaViaCausalAscent

/-- Wherever something is more `r` than something, something is maximal in `r`
(weak `IsMaximumIn`: it has `r` and nothing is more `r` than it).

Proof by well-founded induction along distinct causes of `r`, starting from
the exceeding thing, which has `r` (`hBearer`). A bearer of `r` that nothing
exceeds is the maximum. A bearer that something exceeds has `r` from a
distinct cause (`hExceeded`); that cause is more `r` than it (`hCause`), so it
has `r` (`hBearer`), and the induction hypothesis applies to it
(`hRegress`). Excluded middle decides whether a bearer is exceeded. The
maximum is neither unique nor greatest, nor shown to cause anything. -/
theorem gradesHaveAMaximum {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (hBearer : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hCause : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hExceeded : ExceededPerfectionIsCausedReading InAct MoreIn CausesIn)
    (hRegress : NoInfiniteRegressOfCausesOfAPerfectionReading CausesIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    GradesByApproachToAMaximumReading InAct MoreIn := by
  intro r ⟨x, y, hxy⟩
  have key : ∀ z, InAct z r → ∃ m, IsMaximumIn InAct MoreIn r m := by
    intro z
    refine (hRegress r).induction (C := fun z => InAct z r → ∃ m, IsMaximumIn InAct MoreIn r m)
      z ?_
    intro z ih hz
    rcases hEM (∃ w, MoreIn r w z) with ⟨w, hw⟩ | hNo
    · obtain ⟨c, hne, hc⟩ := hExceeded r z w hz hw
      exact ih c ⟨hne, hc⟩ (hBearer r c z (hCause c z r hne hc))
    · exact ⟨z, hz, fun w hw => hNo ⟨w, hw⟩⟩
  exact key x (hBearer r x y hxy)

/-- Without the bearer premise the other three hold and no grade is maximal. -/
theorem withoutBearer :
    ¬ MoreSuchHasThePerfectionReading WithoutBearer.inAct WithoutBearer.moreIn ∧
    CauseOfQualityInAnotherIsMoreSuchReading WithoutBearer.causesIn WithoutBearer.moreIn ∧
    ExceededPerfectionIsCausedReading WithoutBearer.inAct WithoutBearer.moreIn
      WithoutBearer.causesIn ∧
    NoInfiniteRegressOfCausesOfAPerfectionReading WithoutBearer.causesIn ∧
    NoMaximum WithoutBearer.inAct WithoutBearer.moreIn :=
  ⟨WithoutBearer.bearerFails, WithoutBearer.cause, WithoutBearer.exceeded,
    WithoutBearer.regress, WithoutBearer.noMaximum⟩

/-- Without cause-is-more-such the other three hold and no grade is maximal. -/
theorem withoutCause :
    MoreSuchHasThePerfectionReading WithoutCause.inAct WithoutCause.moreIn ∧
    ¬ CauseOfQualityInAnotherIsMoreSuchReading WithoutCause.causesIn WithoutCause.moreIn ∧
    ExceededPerfectionIsCausedReading WithoutCause.inAct WithoutCause.moreIn
      WithoutCause.causesIn ∧
    NoInfiniteRegressOfCausesOfAPerfectionReading WithoutCause.causesIn ∧
    NoMaximum WithoutCause.inAct WithoutCause.moreIn :=
  ⟨WithoutCause.bearer, WithoutCause.causeFails, WithoutCause.exceeded,
    WithoutCause.regress, WithoutCause.noMaximum⟩

/-- Without exceeded-is-caused the other three hold and no grade is maximal. -/
theorem withoutExceeded :
    MoreSuchHasThePerfectionReading WithoutExceeded.inAct WithoutExceeded.moreIn ∧
    CauseOfQualityInAnotherIsMoreSuchReading WithoutExceeded.causesIn WithoutExceeded.moreIn ∧
    ¬ ExceededPerfectionIsCausedReading WithoutExceeded.inAct WithoutExceeded.moreIn
      WithoutExceeded.causesIn ∧
    NoInfiniteRegressOfCausesOfAPerfectionReading WithoutExceeded.causesIn ∧
    NoMaximum WithoutExceeded.inAct WithoutExceeded.moreIn :=
  ⟨WithoutExceeded.bearer, WithoutExceeded.cause, WithoutExceeded.exceededFails,
    WithoutExceeded.regress, WithoutExceeded.noMaximum⟩

/-- Without the no-regress premise the other three hold and no grade is maximal. -/
theorem withoutRegress :
    MoreSuchHasThePerfectionReading WithoutRegress.inAct WithoutRegress.moreIn ∧
    CauseOfQualityInAnotherIsMoreSuchReading WithoutRegress.causesIn WithoutRegress.moreIn ∧
    ExceededPerfectionIsCausedReading WithoutRegress.inAct WithoutRegress.moreIn
      WithoutRegress.causesIn ∧
    ¬ NoInfiniteRegressOfCausesOfAPerfectionReading WithoutRegress.causesIn ∧
    NoMaximum WithoutRegress.inAct WithoutRegress.moreIn :=
  ⟨WithoutRegress.bearer, WithoutRegress.cause, WithoutRegress.exceeded,
    WithoutRegress.regressFails, WithoutRegress.noMaximum⟩

/-- Zorn form on the homogeneous-scale contrast reading (Mathlib
`zorn_le_nonempty`): if the scale is inhabited and every nonempty chain of
grades has an upper bound on the scale, something is maximal in `r`. The bound
must lie on the scale, so it presupposes a grade at least as high as every
member of the chain. The open interval (0,1) of `INFINITE-GREATEST-WHOLE-CONTROL`
has no maximal grade, so by this theorem it fails the chain condition. No cause
is involved. -/
theorem zornMaximum {Being : Type} {Respect : Type} [Preorder Being]
    {InAct : Being → Respect → Prop} {MoreIn : Respect → Being → Being → Prop}
    {r : Respect} (hScale : HomogeneousScaleReading InAct MoreIn r) [Nonempty Being]
    (hChains : ∀ c : Set Being, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) :
    ∃ m, IsMaximumIn InAct MoreIn r m := by
  obtain ⟨m, hm⟩ := zorn_le_nonempty hChains
  exact ⟨m, (hScale.isMaximumIn_iff_isMax m).2 hm⟩

/-- On a directed homogeneous scale a maximal grade is greatest (Mathlib
`IsMax.isTop`), and on a directed partial order there is at most one. Without
directedness two maximal grades need not be comparable
(`INFINITE-GREATEST-WHOLE-CONTROL`); without antisymmetry tied maxima are
distinct (`MaximumNeedNotBeUnique`). -/
theorem directedMaximalIsGreatest {Being : Type} {Respect : Type} [PartialOrder Being]
    [IsDirectedOrder Being]
    {InAct : Being → Respect → Prop} {MoreIn : Respect → Being → Being → Prop}
    {r : Respect} (hScale : HomogeneousScaleReading InAct MoreIn r) {m : Being}
    (hm : IsMaximumIn InAct MoreIn r m) :
    (∀ x, x ≤ m) ∧ ∀ n, IsMaximumIn InAct MoreIn r n → n = m := by
  have hTop : IsTop m := ((hScale.isMaximumIn_iff_isMax m).1 hm).isTop
  refine ⟨hTop, fun n hn => ?_⟩
  have hnTop : IsTop n := ((hScale.isMaximumIn_iff_isMax n).1 hn).isTop
  exact le_antisymm (hTop n) (hnTop m)

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaGradesFromCausalAscent
