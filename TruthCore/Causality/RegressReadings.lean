import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

/-!
# Two readings of "the series cannot go on to infinity"

The Second Way premise `STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` is
formalized as accessibility of every being under the per se link,
`NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused := ∀ x, Acc
CausesAsCaused x` (Lean core's `WellFounded`, unfolded). The Latin says
something more literal: *non est possibile quod in causis efficientibus
procedatur in infinitum*, that there is no infinite series of efficient causes
each of which causes as caused by the next.

This module states that literal reading separately, as the absence of an
`ℕ`-indexed series whose every member is per se caused by its successor, and
records how the two readings are related. It is an analyst's fidelity check on
the existing formalization (AGENTS.md invariant 8), not a source claim and not
a proof of the premise: neither reading is shown true of any actual
`CausesAsCaused`.

The definitions are generic in the relation, so they apply equally to the
*prima via*'s `NoInfinitePerSeMoverSeriesReading MovesAsMoved`, which has the
same body.
-/

namespace TruthCore.Causality

open TruthCore.Latin.Aquinas.SummaTheologiae

/-- `series` is an infinite descending per se series: for every index `n`, the
member at `n + 1` causes the member at `n` as a caused cause. Index `0` is the
last effect; higher indices go further up the series. Nothing is assumed about
whether the members are distinct. -/
def DescendingPerSeSeries {Being : Type} (CausesAsCaused : Being → Being → Prop)
    (series : Nat → Being) : Prop :=
  ∀ n, CausesAsCaused (series (n + 1)) (series n)

/-- The literal reading of the regress premise: there is no infinite descending
per se series. -/
def NoInfiniteDescendingPerSeSeries {Being : Type}
    (CausesAsCaused : Being → Being → Prop) : Prop :=
  ¬ ∃ series : Nat → Being, DescendingPerSeSeries CausesAsCaused series

/-- For every relation, the corpus's accessibility reading of the regress
premise implies the literal no-infinite-series reading. -/
def AccessibilityReadingExcludesDescendingSeries : Prop :=
  ∀ (Being : Type) (CausesAsCaused : Being → Being → Prop),
    NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused →
      NoInfiniteDescendingPerSeSeries CausesAsCaused

/-- For every relation, the accessibility reading and the literal
no-infinite-series reading of the regress premise are equivalent. The
converse direction (from no infinite series to accessibility) is a theorem of
classical logic, not of constructive logic. -/
def RegressReadingsCoincideClassically : Prop :=
  ∀ (Being : Type) (CausesAsCaused : Being → Being → Prop),
    NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused ↔
      NoInfiniteDescendingPerSeSeries CausesAsCaused

end TruthCore.Causality
