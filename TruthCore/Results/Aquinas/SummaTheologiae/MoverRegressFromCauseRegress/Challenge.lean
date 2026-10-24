import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.MoverRegressFromCauseRegress
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The *prima via*'s regress premise follows from the *secunda via*'s, given that a
per se link of moved movers is a per se link of efficient causes (ST I q.46 a.2
ad 7: stone, stick and hand are its example of per se efficient causes). Every
being is accessible under `MovesAsMoved` because each `MovesAsMoved` step is a
`CausesAsCaused` step, under which every being is accessible. -/
theorem moverRegressFromCauseRegress {Being : Type}
    (MovesAsMoved CausesAsCaused : Being → Being → Prop)
    (hCauseRegress : NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused)
    (hLink : PerSeMoverLinkIsPerSeCauseLinkReading MovesAsMoved CausesAsCaused) :
    NoInfinitePerSeMoverSeriesReading MovesAsMoved := by
  sorry

/-- The cause-regress premise is needed: if moving as moved and causing as caused
are both the successor relation on the natural numbers, the link holds and the
mover series is infinite. -/
theorem needsCauseRegress :
    ¬ ∀ (Being : Type) (MovesAsMoved CausesAsCaused : Being → Being → Prop),
      PerSeMoverLinkIsPerSeCauseLinkReading MovesAsMoved CausesAsCaused →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved := by
  sorry

/-- The link premise is needed: an infinite mover series with no per se causal
links satisfies the cause-regress premise vacuously. -/
theorem needsLink :
    ¬ ∀ (Being : Type) (MovesAsMoved CausesAsCaused : Being → Being → Prop),
      NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.MoverRegressFromCauseRegress
