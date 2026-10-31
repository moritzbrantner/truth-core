import TruthCore.Explanation.AnselmUltimateSource

/-! Source-free premise-strength audit, not an independent defense of Anselm's
or Tapp's common-power commitment. Forget only the power relation; never infer
actual power facts back from through facts. The characterization below is
explicitly relative to global ultimate availability, unlike the local ancestry
composition, which does not assume that premise. -/
namespace TruthCore.Explanation.AnselmCommonSourceAudit
open TruthCore.Explanation.AnselmUltimateSource

/-- One same through-source for EVERY self-through bearer, including those
not assumed ultimate. The common witness is not asserted unique or necessary.
No selfPowerFrom facts appear in this weaker structural condition. -/
def CommonSelfThroughAt (m : Context W B) (w : W) : Prop :=
  ∃ c, ∀ x, m.through w x x → m.through w x c

/-- Equivalence of the structural common-source condition with unique actual
ultimate-source status. This proposition itself omits the four hypotheses of
the theorem establishing it; those stay explicit in that theorem's type. -/
def CommonSelfThroughCharacterizationAt (m : Context W B) (w : W) : Prop :=
  CommonSelfThroughAt m w ↔ UniqueUltimateSourceAt m w

end TruthCore.Explanation.AnselmCommonSourceAudit
