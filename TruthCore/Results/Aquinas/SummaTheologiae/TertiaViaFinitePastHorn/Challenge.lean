import TruthCore.Logic.ExcludedMiddle
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
import TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter13
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaFinitePastHorn
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaContraGentiles
theorem finitePastHorn {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (CausesOrigin : Being → Being → Prop)
    (hEM : ExcludedMiddle)
    (hFinite : PastIsFinite Before now)
    (hInnovating : WhatComesToBeAnewHasInnovatingCauseReading IsAt Before CausesOrigin)
    (hNow : SomethingNowIsReading IsAt now) :
    SomethingHasInnovatingCause CausesOrigin := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaFinitePastHorn
