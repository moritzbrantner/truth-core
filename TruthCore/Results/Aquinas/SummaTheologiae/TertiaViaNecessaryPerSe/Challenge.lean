import TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryBeing.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSe
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryBeing

/-- ST I q.2 a.3 co., the whole *tertia via* on the plenitude reading. Something
is necessary (`tertiaViaSomethingNecessary`). Every necessary being has the cause
of its necessity from elsewhere or not (excluded middle); a cause of a necessary
being's necessity is itself necessary; and there is no infinite regress among
necessary beings caused by another. So every necessary being is necessary per se
or has its necessity, through a finite chain, from something necessary per se;
in particular something is necessary per se. -/
theorem tertiaViaNecessaryPerSe {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (Possible : (Time → Prop) → Prop) (CausesNecessityOf : Being → Being → Prop)
    (hEM : ExcludedMiddle)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hInfinitePast : PastIsInfinite Before now)
    (hCollective : AllCanNotBeThenNothingPossibleReading Possible IsAt)
    (hBegin : NothingBeginsExceptThroughWhatIsReading IsAt Before)
    (hNow : SomethingNowIsReading IsAt now)
    (hCauseNecessary :
      CauseOfNecessityIsNecessaryReading Possible IsAt CausesNecessityOf)
    (hNoRegress :
      NoInfiniteRegressInCausedNecessariesReading Possible IsAt CausesNecessityOf) :
    NecessaryPerSeBeingReading Possible IsAt CausesNecessityOf := by
  sorry

/-- The no-regress premise is needed. Times are the natural numbers counted
backwards from `now = 0` (a larger number is earlier). Every being always is (so is necessary)
and `n + 1` causes the necessity of `n`: an infinite descending series of caused
necessaries with no being necessary per se, while every other premise holds. -/
theorem withoutNoRegressNoPerSe :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop)
      (CausesNecessityOf : Being → Being → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      PastIsInfinite Before now →
      AllCanNotBeThenNothingPossibleReading Possible IsAt →
      NothingBeginsExceptThroughWhatIsReading IsAt Before →
      SomethingNowIsReading IsAt now →
      CauseOfNecessityIsNecessaryReading Possible IsAt CausesNecessityOf →
      NecessaryPerSeBeingReading Possible IsAt CausesNecessityOf := by
  sorry

/-- The premise that a cause of necessity is itself necessary is needed. `true`
always is and `false` never is; `false` causes the necessity of `true`. The
regress premise holds (no caused necessary has a necessary cause), every other
premise holds, and nothing is necessary per se. -/
theorem withoutNecessaryCauseNoPerSe :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop)
      (CausesNecessityOf : Being → Being → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      PastIsInfinite Before now →
      AllCanNotBeThenNothingPossibleReading Possible IsAt →
      NothingBeginsExceptThroughWhatIsReading IsAt Before →
      SomethingNowIsReading IsAt now →
      NoInfiniteRegressInCausedNecessariesReading Possible IsAt CausesNecessityOf →
      NecessaryPerSeBeingReading Possible IsAt CausesNecessityOf := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSe
