module

public import Mathlib.Algebra.Order.Field.Rat
public import TruthCore.Science.InductionSelection
public import TruthCore.Logic.TranscendentalPractice
import Mathlib.Tactic.NormNum

/-! Analyst reconstruction for #934; attribution deferred. Two incompatible,
exhaustive hypotheses are represented by their probability for W and its
complement for V. This finite Bayesian policy is stipulated, not independently
obligatory. The two likelihoods concern the SAME observed event, not a
normalization across hypotheses. All probabilities here are rational numbers.
Truth, social attraction, community identity and probability are separate. -/

@[expose] public section
namespace TruthCore.Logic.ContrastiveWorldview

/-- Non-dogmatic prior and positive, at-most-one likelihoods. Strict positivity
keeps conditional probabilities and odds defined. Zero-likelihood cases and
nonexhaustive worldview spaces require a separate profile. -/
structure Comparison where
  prior : ℚ
  likelihoodW : ℚ
  likelihoodV : ℚ
  prior_pos : 0 < prior
  prior_lt_one : prior < 1
  likelihoodW_pos : 0 < likelihoodW
  likelihoodW_le_one : likelihoodW ≤ 1
  likelihoodV_pos : 0 < likelihoodV
  likelihoodV_le_one : likelihoodV ≤ 1

def normalizer (c : Comparison) : ℚ :=
  c.prior * c.likelihoodW + (1 - c.prior) * c.likelihoodV

def posteriorW (c : Comparison) : ℚ := c.prior * c.likelihoodW / normalizer c
def posteriorV (c : Comparison) : ℚ := (1 - c.prior) * c.likelihoodV / normalizer c

/-- Relabel both hypotheses, including the prior. Swapping a speaker's birthplace
alone instead leaves the entire Comparison unchanged. -/
def swap (c : Comparison) : Comparison where
  prior := 1 - c.prior
  likelihoodW := c.likelihoodV
  likelihoodV := c.likelihoodW
  prior_pos := sub_pos.mpr c.prior_lt_one
  prior_lt_one := sub_lt_self 1 c.prior_pos
  likelihoodW_pos := c.likelihoodV_pos
  likelihoodW_le_one := c.likelihoodV_le_one
  likelihoodV_pos := c.likelihoodW_pos
  likelihoodV_le_one := c.likelihoodW_le_one

/-- The comparison rule has no community input. This models a declared public
standard, not the empirical claim that agents actually ignore their identity. -/
def publicAssessment {Community : Type} (_ : Community) (c : Comparison) : ℚ :=
  posteriorW c

/-- Actual truth and attraction do not enter the update policy. -/
structure Case where
  comparison : Comparison
  trueHypothesis : Bool
  attractiveHypothesis : Bool
  inheritedHypothesis : Bool

def neutral : Comparison := ⟨1/2, 1/2, 1/2, by norm_num, by norm_num,
  by norm_num, by norm_num, by norm_num, by norm_num⟩
def inheritedPrior : Comparison := ⟨3/4, 1/2, 1/2, by norm_num, by norm_num,
  by norm_num, by norm_num, by norm_num, by norm_num⟩
/-- A likelihood ratio of three favors W, but its prior odds of one to nine
leave W short of being the posterior winner. -/
def evidenceGain : Comparison := ⟨1/10, 3/4, 1/4, by norm_num, by norm_num,
  by norm_num, by norm_num, by norm_num, by norm_num⟩
/-- A binary testimony channel: for each true hypothesis the corresponding
report is received with probability 3/4, the other with 1/4. Hearing W is
informative even when that testimony is culturally inherited. -/
def testimonyLikelihood (truth report : Bool) : ℚ := if truth = report then 3/4 else 1/4

def testimony : Comparison := ⟨1/2, testimonyLikelihood true true,
  testimonyLikelihood false true, by norm_num, by norm_num,
  by norm_num [testimonyLikelihood], by norm_num [testimonyLikelihood],
  by norm_num [testimonyLikelihood], by norm_num [testimonyLikelihood]⟩

def reliableInherited : Case := ⟨testimony, true, false, true⟩
/-- The same reliable channel can produce an erroneous positive report. -/
def misleadingInherited : Case := ⟨testimony, false, true, true⟩

def falseAttractive : Case := ⟨inheritedPrior, false, true, true⟩
def indistinguishable (truth : Bool) : Case := ⟨neutral, truth, false, false⟩

/-- A coherent membership convention: each community authorizes its own
proposal. This is not defined as public truth or categorical authority. -/
def insiderStandard (community proposal : Bool) : Prop := community = proposal

def LocalStandardControls : Prop :=
  (∀ community, insiderStandard community community) ∧
  insiderStandard true true ∧ ¬ insiderStandard false true ∧
  ¬ (∀ a b proposal, insiderStandard a proposal ↔ insiderStandard b proposal)

/-- Algebraic constraints conditional on this update policy: normalization,
posterior odds, equal-likelihood prior preservation, strict evidence gain and
posterior winner are distinct comparisons. -/
def UpdateConstraints : Prop := ∀ c : Comparison,
  0 < normalizer c ∧ posteriorW c + posteriorV c = 1 ∧
  posteriorW c / posteriorV c =
    (c.prior / (1 - c.prior)) * (c.likelihoodW / c.likelihoodV) ∧
  (c.likelihoodW = c.likelihoodV → posteriorW c = c.prior) ∧
  (c.prior < posteriorW c ↔ c.likelihoodV < c.likelihoodW) ∧
  (posteriorV c < posteriorW c ↔
    (1 - c.prior) * c.likelihoodV < c.prior * c.likelihoodW) ∧
  (c.prior = 1/2 → (posteriorV c < posteriorW c ↔ c.likelihoodV < c.likelihoodW)) ∧
  (c.likelihoodW = c.likelihoodV → posteriorV c < posteriorW c → 1/2 < c.prior)

def IdentityControls : Prop :=
  (∀ c, posteriorW (swap c) = posteriorV c) ∧
  (∀ (Community : Type) (a b : Community) c,
    publicAssessment a c = publicAssessment b c) ∧
  (∀ answer : Unit → Bool → Prop,
    Science.InductionSelection.Neutral Science.InductionSelection.symmetric answer →
    ∀ h, ¬ Science.InductionSelection.SingletonAt answer () h)

/-- Concrete non-entailments on inhabited two-hypothesis cases. Reliability
means this channel's truth-conditional rate, not factive testimony or a defense
of a particular inherited tradition. -/
def CaseControls : Prop :=
  posteriorW neutral = 1/2 ∧ posteriorW inheritedPrior = 3/4 ∧
  posteriorW evidenceGain = 1/4 ∧
  evidenceGain.prior < posteriorW evidenceGain ∧
  posteriorW evidenceGain < posteriorV evidenceGain ∧
  (∀ truth, testimonyLikelihood truth false + testimonyLikelihood truth true = 1) ∧
  (∀ truth, 1/2 < testimonyLikelihood truth truth) ∧
  posteriorW reliableInherited.comparison = 3/4 ∧
  posteriorV misleadingInherited.comparison < posteriorW misleadingInherited.comparison ∧
  misleadingInherited.trueHypothesis ≠ misleadingInherited.inheritedHypothesis ∧
  0 < testimonyLikelihood misleadingInherited.trueHypothesis true ∧
  reliableInherited.inheritedHypothesis = reliableInherited.trueHypothesis ∧
  falseAttractive.trueHypothesis ≠ falseAttractive.attractiveHypothesis ∧
  posteriorV falseAttractive.comparison < posteriorW falseAttractive.comparison ∧
  (indistinguishable true).comparison = (indistinguishable false).comparison ∧
  (indistinguishable true).trueHypothesis ≠ (indistinguishable false).trueHypothesis

/-- Reuse exact access-versus-duty and instrumental-success-versus-duty
boundaries, not a new disguised assumption that public standards bind everyone.
A neutral response is policy-relative; categorical authority remains additional. -/
def CoreCertificate : Prop :=
  UpdateConstraints ∧ IdentityControls ∧ CaseControls ∧ LocalStandardControls

def Certificate : Prop := CoreCertificate ∧
  CorrectionCriterion.CriterionCharacterizationAndControls ∧
  TranscendentalPractice.InquiryAccessBoundary ∧
  TranscendentalPractice.AgencyDutyBoundary ∧
  ReflectiveCoherence.TruthDirectedReflectiveDuty

end TruthCore.Logic.ContrastiveWorldview
