import TruthCore.Logic.ThirdFactorTracking

/-! The third-factor union bound, exact binary error accounting, the subclass
gap bound and the finite sharpness, cancellation and hard-case models for
#1586. No independence between the error events is assumed. -/

namespace TruthCore.Results.Logic.ThirdFactorTracking
open TruthCore.Logic.ThirdFactorTracking
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Third-factor union bound on one common distribution, without independence:
`{B ≠ M} ⊆ {B ≠ F} ∪ {F ≠ M}` and subadditivity. Values may be of any type. -/
theorem thirdFactorUnionBound {Ω V : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (B F M : Ω → V) (e₁ e₂ : ℝ≥0∞) :
    SelectionErrorAtMost μ B F e₁ →
    FactorTruthGapAtMost μ F M e₂ →
    JudgmentTruthAgreementAtLeast μ B M (e₁ + e₂) := by
  sorry

/-- One-sided third-factor bound: a wrongly endorsed act is endorsed against the
factor or favoured by the factor without a reason. No independence. -/
theorem oneSidedThirdFactorBound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (B F M : Ω → Bool) (d₁ d₂ : ℝ≥0∞) :
    EndorsedAgainstFactorAtMost μ B F d₁ →
    FactorWithoutReasonAtMost μ F M d₂ →
    EndorsedWithoutReasonAtMost μ B M (d₁ + d₂) := by
  sorry

/-- Exact binary error accounting: two errors cancel. -/
theorem binaryErrorAccounting : BinaryErrorAccounting := by
  sorry

/-- The gap on a measurable class is at most the aggregate gap divided by the
class weight. -/
theorem subclassGapBound : SubclassGapBound := by
  sorry

/-- Sharpness, cancellation and hard-case concentration in four stipulated cases. -/
theorem thirdFactorModels : ThirdFactorModels := by
  sorry

end TruthCore.Results.Logic.ThirdFactorTracking
