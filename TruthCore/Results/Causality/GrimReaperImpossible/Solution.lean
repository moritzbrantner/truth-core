import TruthCore.Causality.GrimReaper

namespace TruthCore.Results.Causality.GrimReaperImpossible
open TruthCore.Causality

/-- The contradiction requires the Reaper *rule* as well as an unbounded
earlier-than ordering; no well-foundedness of efficient causes is presumed. -/
theorem grimReaperImpossible : NoFirstGrimReaperSchedule := by
  rintro ⟨acts, hLaw⟩
  have noActs : ∀ n, ¬ acts n := by
    intro n hn
    have noEarlier := (hLaw n).mp hn
    have nextActs : acts (n + 1) := (hLaw (n + 1)).mpr (by
      intro m hEarlier
      exact noEarlier m (Nat.lt_trans (Nat.lt_succ_self n) hEarlier))
    exact noEarlier (n + 1) (Nat.lt_succ_self n) nextActs
  have zeroActs : acts 0 := (hLaw 0).mpr (by
    intro m _
    exact noActs m)
  exact noActs 0 zeroActs

end TruthCore.Results.Causality.GrimReaperImpossible
