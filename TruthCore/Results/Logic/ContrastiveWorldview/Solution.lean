module
public import TruthCore.Logic.ContrastiveWorldview
public import TruthCore.Results.Science.InductionSelection.Solution
public import TruthCore.Results.Logic.CorrectionCriterion.Solution
public import TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess.Solution
public import TruthCore.Results.Logic.TranscendentalPractice.AgencyDuty.Solution
public import TruthCore.Results.Logic.ReflectiveCoherence.TruthDirected.Solution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace TruthCore.Results.Logic.ContrastiveWorldview
open TruthCore.Logic.ContrastiveWorldview

private theorem normalizer_pos (c : Comparison) : 0 < normalizer c :=
  add_pos (mul_pos c.prior_pos c.likelihoodW_pos)
    (mul_pos (sub_pos.mpr c.prior_lt_one) c.likelihoodV_pos)

/-- Normalized two-hypothesis Bayes algebra; no epistemic ought is inferred. -/
theorem updateConstraints : UpdateConstraints := by
  intro c
  have hz := normalizer_pos c
  have hp := c.prior_pos
  have hq := sub_pos.mpr c.prior_lt_one
  have hw := c.likelihoodW_pos
  have hv := c.likelihoodV_pos
  have hZ : normalizer c ≠ 0 := ne_of_gt hz
  have hP : c.prior ≠ 0 := ne_of_gt hp
  have hQ : 1 - c.prior ≠ 0 := ne_of_gt hq
  have hV : c.likelihoodV ≠ 0 := ne_of_gt hv
  refine ⟨hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold posteriorW posteriorV
    rw [← add_div]
    exact div_self hZ
  · unfold posteriorW posteriorV
    field_simp
  · intro he
    apply (div_eq_iff hZ).mpr
    dsimp [normalizer]
    rw [he]
    ring
  · unfold posteriorW
    rw [lt_div_iff₀ hz]
    dsimp [normalizer]
    constructor <;> intro h
    · nlinarith [mul_pos hp hq]
    · nlinarith [mul_pos (mul_pos hp hq) (sub_pos.mpr h)]
  · unfold posteriorW posteriorV
    exact div_lt_div_iff_of_pos_right hz
  · intro he
    unfold posteriorW posteriorV
    rw [div_lt_div_iff_of_pos_right hz, he]
    constructor <;> intro h <;> linarith
  · intro he hwin
    have hn := (div_lt_div_iff_of_pos_right hz).mp hwin
    rw [he] at hn
    nlinarith

/-- Identity neutrality reuses the generic #1037 fixed-evidence theorem. -/
theorem identityControls : IdentityControls := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    unfold posteriorW posteriorV normalizer swap
    congr 1; ring
  · intro Community a b c
    rfl
  · intro answer hn h hs
    have fixed := (TruthCore.Results.Science.InductionSelection.symmetry
      Unit Bool TruthCore.Science.InductionSelection.symmetric answer () hn rfl).2 h hs
    cases h <;> cases fixed

/-- Concrete controls keep truth, inherited access and attractiveness distinct. -/
theorem caseControls : CaseControls := by
  unfold CaseControls
  norm_num [posteriorW, posteriorV, normalizer, neutral, inheritedPrior,
    evidenceGain, reliableInherited, falseAttractive, indistinguishable,
    testimony, testimonyLikelihood, misleadingInherited]

theorem localStandardControls : LocalStandardControls := by
  refine ⟨fun _ => rfl, rfl, by simp [insiderStandard], ?_⟩
  intro h
  exact (by simp [insiderStandard] : ¬ insiderStandard false true) ((h true false true).mp rfl)

/-- Conditional consequence, identity-swap constraint and finite omission
controls, composed with the existing access and normative-authority results. -/
theorem certificate : Certificate :=
  ⟨⟨updateConstraints, identityControls, caseControls, localStandardControls⟩,
    TruthCore.Results.Logic.CorrectionCriterion.characterization,
    TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess.boundary,
    TruthCore.Results.Logic.TranscendentalPractice.AgencyDuty.boundary,
    TruthCore.Results.Logic.ReflectiveCoherence.TruthDirected.truthDirectedReflectiveDuty⟩
end TruthCore.Results.Logic.ContrastiveWorldview
