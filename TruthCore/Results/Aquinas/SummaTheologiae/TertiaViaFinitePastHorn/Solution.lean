import TruthCore.Logic.ExcludedMiddle
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
import TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter13
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaFinitePastHorn
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaContraGentiles

/-- The finite-past horn of SCG I.13 [30]. Let `t` be a time up to now with no
earlier time, and `x` something that is now. If `x` is at `t`, then, being in
time at a first instant, it began with time (open premise); if not, `t` is
earlier than now and `x` is not at `t` but is now. Either way `x` comes to be
anew, so its coming to be has an innovating cause other than itself. -/
theorem finitePastHorn {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (BeganWithTime : Being → Prop) (CausesOrigin : Being → Being → Prop)
    (hEM : ExcludedMiddle)
    (hFinite : PastIsFinite Before now)
    (hBegan : TemporalBeingsAtTheFirstTimeBeganWithTime IsAt Before BeganWithTime)
    (hInnovating : WhatComesToBeAnewHasInnovatingCauseReading IsAt Before BeganWithTime
      CausesOrigin)
    (hNow : SomethingNowIsReading IsAt now) :
    SomethingHasInnovatingCause CausesOrigin := by
  obtain ⟨t, hUpToNow, hFirst⟩ := hFinite
  obtain ⟨x, hx⟩ := hNow
  -- INF-SCG-I-13-SOMETHING-COMES-TO-BE-ANEW
  have hAnew : ComesToBeAnew IsAt Before BeganWithTime x := by
    cases hEM (IsAt x t) with
    | inl h => exact Or.inr (hBegan x t h hFirst)
    | inr h =>
      rcases hUpToNow with hNowTime | hBefore
      · exact absurd (hNowTime ▸ hx) h
      · exact Or.inl ⟨t, now, hBefore, h, hx⟩
  -- INF-SCG-I-13-INNOVATING-CAUSE
  obtain ⟨c, hOther, hCause⟩ := hInnovating x hAnew
  exact ⟨x, c, hOther, hCause⟩

end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaFinitePastHorn
