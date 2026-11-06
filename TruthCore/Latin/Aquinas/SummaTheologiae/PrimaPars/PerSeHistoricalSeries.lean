module

public import TruthCore.Causality.RegressReadings

/-!
Analyst distinction for #1112. `E y x` is a primitive essential-dependence
link, and `H y x` a proposed historical-predecessor link. Neither name proves
causal applicability. Present simultaneity and loss of causal power on removal
of a cause remain OPEN: they need time and intervention vocabulary, not just a
binary relation. Well-foundedness is a separate premise, never part of the
definition of a link or a stipulation that a first member already exists.

The source-derived `InfiniteRegressImpossibleOnlyInPerSeSeriesReading` stays
unchanged. Its two proposition parameters do not encode this distinction.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality

/-- Every proposed historical step is an essential-dependence step. This is
an explicit, disputable dictionary, not a consequence of the word "cause". -/
def HistoricalLinksAreEssential {Being : Type} (H E : Being → Being → Prop) : Prop :=
  ∀ y x, H y x → E y x

/-- If historical links really are essential links, well-founded essential
dependence excludes a historical Nat-indexed descent. No WF premise is proved. -/
def HistoricalDescentExcludedByEssentialDictionary : Prop :=
  ∀ (Being : Type) (H E : Being → Being → Prop),
    NoInfinitePerSeEfficientCauseSeriesReading E →
    HistoricalLinksAreEssential H E → NoInfiniteDescendingPerSeSeries H

/-- Concrete relation-level compatibility on the SAME historical members:
every `some n` essentially depends on `none`, while history descends through
the distinct members `some n`. Essential dependence is nonempty and accessible;
historical descent is infinite, injective, and has a predecessor at every
historical member. No historical edge is essential in this witness.
This stipulates neither a temporal interpretation nor metaphysical possibility.
`none` is a first essential source in the model, not in the definitions. -/
def EssentialDependenceCompatibleWithHistoricalDescent : Prop :=
  ∃ E H : Option Nat → Option Nat → Prop,
    NoInfinitePerSeEfficientCauseSeriesReading E ∧
    (∀ n, E none (some n)) ∧
    DescendingPerSeSeries H (fun n => some n) ∧
    (∀ i j : Nat, (some i : Option Nat) = some j → i = j) ∧
    (∀ n, ∃ m, H (some m) (some n)) ∧
    (∀ y x, H y x → ¬ E y x)

/-- A typed analyst sibling of the old two-Prop source transcription: the
dictionary has consequences, and dropping it admits the explicit witness. -/
def PerSeHistoricalSeriesDistinction : Prop :=
  HistoricalDescentExcludedByEssentialDictionary ∧
  EssentialDependenceCompatibleWithHistoricalDescent

end TruthCore.Latin.Aquinas.SummaTheologiae
