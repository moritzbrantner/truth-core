import TruthCore.Comparison.McTaggart
import TruthCore.Observation.Change
namespace TruthCore.Results.Alternatives.McTaggartDefeatedByChange
open TruthCore.Alternatives.McTaggart
open TruthCore.Observation.Change

/-- McTaggart's bundle on change is defeated by consequence against F3 (#1007).
Its two sourced commitments together entail that nothing changes: if anything
changed, by "all change is A-series change" some event would change in its
A-series determinations, which "no event changes in its A-series
determinations" denies. So, given that something changes, at least one of the
two commitments is false (modus tollens). No opining, motion or bridge premise
is used. The defeat holds relative to F3's floor marking, and it reaches only
the 1908 bundle: McTaggart's later reply (*The Nature of Existence* II, § 511,
`AppearingsDoNotChangeReading`) says only that appearers do not change, which
is compatible with F3 as stated (a changing non-opiner is a witness), so that
reply is not defeated here. -/
theorem bundleDefeatedByChange {Being : Type}
    (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
    (Changes : Being → Prop)
    (hChange : SomethingChangesReading Changes) :
    UnrealityOfTimeFalse ASeriesChanges Opines Changes := by
  rintro ⟨⟨hNoASeriesChange, _⟩, hAllChange⟩
  obtain ⟨x, hx⟩ := hChange
  -- All change is A-series change: some event changes in its A-determinations.
  obtain ⟨e, hASeries⟩ := hAllChange x hx
  exact hNoASeriesChange e hASeries

/-- F3 is needed: where one being opines and nothing changes, McTaggart's
bundle holds. -/
theorem needsSomethingChanges :
    ¬ ∀ (Being : Type) (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
        (Changes : Being → Prop),
      UnrealityOfTimeFalse ASeriesChanges Opines Changes := by
  intro h
  exact h Unit (fun _ => False) (fun _ _ => True) (fun _ => False)
    ⟨⟨fun _ hASeries => hASeries, (), True, trivial⟩, fun _ hChanges => hChanges.elim⟩
end TruthCore.Results.Alternatives.McTaggartDefeatedByChange
