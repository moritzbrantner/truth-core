import TruthCore.Logic.ExcludedMiddle
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryBeing
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.2 a.3 co., the *tertia via* up to *oportet aliquid esse necessarium*,
on the plenitude reading. If everything could not-be, then (collective
possibility) it would be possible that nothing is; with an infinite past, that
possibility has been realized (plenitude), so once nothing was. But what is not
begins only through what is, so nothing would be now; yet something is. So not
everything can not-be, and (excluded middle) something is necessary. -/
theorem tertiaViaSomethingNecessary {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (Possible : (Time → Prop) → Prop)
    (hEM : ExcludedMiddle)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hInfinitePast : PastIsInfinite Before now)
    (hCollective : AllCanNotBeThenNothingPossibleReading Possible IsAt)
    (hBegin : NothingBeginsExceptThroughWhatIsReading IsAt Before)
    (hNow : SomethingNowIsReading IsAt now) :
    SomethingIsNecessaryReading Possible IsAt := by
  sorry

/-- On the plenitude reading, the distributive reading of *quod possibile est non
esse, quandoque non est* follows: plenitude over an infinite past entails that
each thing that can not-be at some (past) time is not. The plenitude reading is
the stronger of the two sibling readings. -/
theorem plenitudeYieldsDistributive {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (Possible : (Time → Prop) → Prop)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hInfinitePast : PastIsInfinite Before now) :
    WhatCanNotBeSometimeIsNotReading Possible IsAt := by
  sorry

/-- The collective-possibility premise is needed, and the distributive reading
does not license the step (the quantifier-shift objection). Relay model: times
are the natural numbers counted backwards from `now = 0` (a larger number is an
earlier time, so the past is infinite), and being `n` is only at time `n`;
possible means realized at some past time. Plenitude, an infinite past, "nothing
begins except through what is", "something now is" and the distributive reading
all hold, every being can not-be, and nothing is necessary. -/
theorem relayWithoutCollectivePossibility :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      PastIsInfinite Before now →
      NothingBeginsExceptThroughWhatIsReading IsAt Before →
      SomethingNowIsReading IsAt now →
      WhatCanNotBeSometimeIsNotReading Possible IsAt →
      SomethingIsNecessaryReading Possible IsAt := by
  sorry

/-- The infinite past is needed. Finite past: a single being that is only at the
first time, `now = 0`. The plenitude premise holds vacuously, collective
possibility, "nothing begins except through what is" and "something now is"
hold, and the being can not-be. -/
theorem finitePastNoNecessaryBeing :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      AllCanNotBeThenNothingPossibleReading Possible IsAt →
      NothingBeginsExceptThroughWhatIsReading IsAt Before →
      SomethingNowIsReading IsAt now →
      SomethingIsNecessaryReading Possible IsAt := by
  sorry

/-- "Nothing begins except through what is" is needed. Times as in
`relayWithoutCollectivePossibility`; a single being that is only now, after
nothing was: every other premise holds and the being can not-be. -/
theorem withoutNothingFromNothingNoNecessaryBeing :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      PastIsInfinite Before now →
      AllCanNotBeThenNothingPossibleReading Possible IsAt →
      SomethingNowIsReading IsAt now →
      SomethingIsNecessaryReading Possible IsAt := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryBeing
