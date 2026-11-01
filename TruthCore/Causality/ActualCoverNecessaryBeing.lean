import TruthCore.Causality.ActualFusionNecessaryBeing
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Explanation.WellFoundedSource

/-!
Analyst weakening of the selected-family fusion/nonoverlap route. Reuses the
SAME actual no-necessary-parts family, Ontic, order, Covers and cause relation.
Actual coverage does not assert a fusion or no-extra-parts property; a cause
not being part of its effect does not assert absence of every common part.
No source assertion, metaphysical application or default warrant is established.
-/
namespace TruthCore.Causality.ActualCoverNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Mereology.UniversalFusionBoundary

/-- Explicit actual candidate plus coverage of this SAME selected family.
No fusion, no-extra-parts clause, ordinary contingency or causal role follows. -/
def ActualCoverAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (cover : B) : Prop :=
  m.ExistsAt w cover ∧ Covers (ActualNoNecessaryPartsFamily m w) cover

/-- Formation for this one nonempty actual family, not every set or a
presupposed actual no-necessary-parts population or unconditional cover. -/
def ConditionalActualCoverAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) : Prop :=
  (ActualNoNecessaryPartsFamily m w).Nonempty → ∃ cover, ActualCoverAt m w cover

/-- Explicit OPEN restriction on the unchanged primitive cause relation.
Only cause-as-part is excluded; nonoverlap is not assumed or inferred. -/
def CauseNotPartOfEffectAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) : Prop :=
  ∀ c e, m.Causes w c e → ¬ c ≤ e

end TruthCore.Causality.ActualCoverNecessaryBeing
