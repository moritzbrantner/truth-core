import TruthCore.Causality.PossibleCauseOfContingency
import TruthCore.Mereology.UniversalFusionBoundary

/-!
Analyst application of NecessaryBeing survey A1's outside-contingents step.
Materialized witnesses NECESSARYBEING-A1-TOTALITY and NECESSARYBEING-A1-EXTERNAL
motivate the question; these definitions are not attributed source readings.
Covers does not assert a fusion exists or is contingent. The concrete predicate,
rigid identity, existence and primitive Causes retain the imported Scenario's
meaning. Causes is not identified with existential grounding or temporal
precedence. Actual cause occurrence and coverage are independent OPEN premises.
See docs/necessarybeing-survey-inventory.md for source/application boundaries.
-/
namespace TruthCore.Causality.ContingentTotalityCause
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Mereology.UniversalFusionBoundary

/-- Every actual contingent concretum is a part of the selected candidate whole.
No existence, contingency, fusion or causal condition on the whole is inferred. -/
def ContingentsCovered {W B : Type} [PartialOrder B]
    (s : Scenario W B) (w : W) (whole : B) : Prop :=
  Covers (fun x => s.concrete x ∧ ContingentAt s.ontic w x) whole

/-- Actual concrete cause of a selected object at one world. The relation is
primitive Causes, not a necessitating sufficient reason or a temporal law. -/
def ActualConcreteCause {W B : Type} (s : Scenario W B) (w : W)
    (c x : B) : Prop :=
  s.concrete c ∧ s.ontic.ExistsAt w c ∧ s.ontic.Causes w c x

/-- Some actual concrete cause of the selected whole lies outside its parts.
This does not follow from numerical distinction or from local member causation. -/
def ExternalWholeCause {W B : Type} [PartialOrder B]
    (s : Scenario W B) (w : W) (whole : B) : Prop :=
  OutsideCause (ActualConcreteCause s w) whole

/-- One and the same witness actually exists, is concrete, is necessary in
all accessible worlds and causes the selected whole at the selected world.
No causal relation at another world, unity or underivedness is concluded. -/
def NecessaryWholeCause {W B : Type} (s : Scenario W B) (w : W)
    (whole : B) : Prop :=
  ∃ c, s.concrete c ∧ s.ontic.ExistsAt w c ∧
    NecessaryAt s.ontic w c ∧ s.ontic.Causes w c whole

end TruthCore.Causality.ContingentTotalityCause
