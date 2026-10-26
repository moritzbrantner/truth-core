import TruthCore.Case.Catholicism.StageOne.CausalFinitism
import TruthCore.Results.Bridges.PerSeRegressFiniteGrounding.Solution
import TruthCore.Results.Causality.FiniteGroundingHasSource.Solution

namespace TruthCore.Results.Case.Catholicism.CausalFinitism
open TruthCore.Case.Catholicism.StageOne.CausalFinitism
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Finite distinct ancestry and loop exclusion imply the existing per se
accessibility reading, provided each per se edge belongs to that causal relation.
All three premises remain philosophically open; no source attribution is made. -/
theorem perSeNoRegressOfFiniteAncestry {Being : Type}
    (cause perSe : Being → Being → Prop)
    (finiteHistory : FiniteDistinctAncestry cause)
    (noLoops : NoCausalLoops cause)
    (included : PerSeLinksIncluded cause perSe) :
    NoInfinitePerSeEfficientCauseSeriesReading perSe := by
  sorry
theorem needsNoLoops :
    ∃ (cause perSe : Unit → Unit → Prop),
      FiniteDistinctAncestry cause ∧ PerSeLinksIncluded cause perSe ∧
        ¬ NoInfinitePerSeEfficientCauseSeriesReading perSe := by
  sorry
theorem needsFiniteAncestry :
    ∃ (cause perSe : Nat → Nat → Prop),
      NoCausalLoops cause ∧ PerSeLinksIncluded cause perSe ∧
        ¬ NoInfinitePerSeEfficientCauseSeriesReading perSe := by
  sorry
theorem needsInclusion :
    ∃ (cause perSe : Unit → Unit → Prop),
      FiniteDistinctAncestry cause ∧ NoCausalLoops cause ∧
        ¬ NoInfinitePerSeEfficientCauseSeriesReading perSe := by
  sorry
/-- Compose the new accessibility result with the existing finite-grounding
and regress-to-finite-path results. The endpoint may vary with the starting being and is
uncaused only with respect to the supplied per se relation. -/
theorem finitePathsOfFiniteAncestry {Being : Type}
    (cause perSe : Being → Being → Prop)
    (finiteHistory : FiniteDistinctAncestry cause)
    (noLoops : NoCausalLoops cause)
    (included : PerSeLinksIncluded cause perSe) :
    TruthCore.Bridges.EveryBeingHasFinitePerSePathToUncaused perSe := by
  sorry

end TruthCore.Results.Case.Catholicism.CausalFinitism
