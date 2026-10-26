import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
namespace TruthCore.Results.Bridges.TertiaPlenitudePossibleNotBeSometimeIsNot
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Bridge (#401): the tertia via's "what can not-be, at some time is not"
(`STMT-WHAT-CAN-NOT-BE-SOMETIME-IS-NOT`) follows from the plenitude principle
over an infinite past (`STMT-PLENITUDE-OVER-INFINITE-PAST`) together with an
infinite past (`STMT-PAST-IS-INFINITE`). For a being that can not-be, the
possibility of its not being is realized at some past time; so at some time it
is not. The bridge uses only the past time that plenitude supplies, not its
being before now. -/
theorem whatCanNotBeSometimeIsNotOfPlenitude {Being Time : Type}
    (Before : Time → Time → Prop) (now : Time)
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hInfinite : PastIsInfinite Before now) :
    WhatCanNotBeSometimeIsNotReading Possible IsAt := by
  intro x hCanNotBe
  -- Plenitude realizes the possibility `fun t => ¬ IsAt x t` at some past time.
  obtain ⟨t, _hBefore, hNot⟩ := hPlenitude hInfinite (fun t => ¬ IsAt x t) hCanNotBe
  exact ⟨t, hNot⟩
end TruthCore.Results.Bridges.TertiaPlenitudePossibleNotBeSometimeIsNot
