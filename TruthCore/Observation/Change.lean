module

@[expose] public section

/-!
Floor candidate F3 (#1007): something changes, in McTaggart's general sense
of change (`DEF-CHANGE-GENERAL`: a thing changes in some characteristic,
quality or relation, the thoughts of conscious beings included).

The owner approved F3 on the observation basis (2026-11-05). Its marking waits
for a pinned text that states it in this general sense: Aquinas' *aliqua
moveri* states motion as reduction from potency to act, and identifying
Aristotle's μεταβολή with McTaggart's "change" is a reading step no source
states (`TruthCore.Alternatives.McTaggart`). Its recorded rival is McTaggart's
bundle on change.
-/

namespace TruthCore.Observation.Change

universe u

/-- F3: something changes, in the general sense. `Changes` is the same
parameter as McTaggart's `Changes` (`DEF-CHANGE-GENERAL`); it is neither
A-series change nor reduction from potency to act. -/
def SomethingChangesReading {Being : Sort u} (Changes : Being → Prop) : Prop :=
  ∃ x, Changes x

end TruthCore.Observation.Change
