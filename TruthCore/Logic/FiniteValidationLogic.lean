module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic.NormNum

/-! Analyst formulation for #1066 under #931; attribution deferred.
A hypothesis predicts a binary label on a finite domain. Actual error is its
probability of disagreement with an independently supplied truthful label.
Validation samples use the genuine independent product of the SAME deployment
measure. This sampling-to-reality bridge is OPEN in applications. The pool is
fixed independently of validation data; a procedure may abstain if none passes.
The bound controls a joint false-acceptance event across samples, not posterior
confidence conditional on passing, factive warrant, or categorical epistemic duty.
-/

@[expose] public section
namespace TruthCore.Logic.FiniteValidationLogic
open MeasureTheory
open scoped ENNReal

/-- Actual disagreement probability under the supplied deployment distribution. -/
def error {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (truth h : Ω → Bool) : ℝ≥0∞ := μ {x | h x ≠ truth x}

/-- Zero validation disagreements. Truthful labels are an explicit input. -/
def passes {Ω : Type} (truth h : Ω → Bool) (n : ℕ) : Set (Fin n → Ω) :=
  {sample | ∀ i, h (sample i) = truth (sample i)}

/-- Independent, identically distributed validation draws from deployment μ. -/
noncomputable def sampling {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) : Measure (Fin n → Ω) := Measure.pi (fun _ => μ)

/-- Some bad member of the predeclared pool passes. The pool may be empty;
selection among its passing members is allowed. No good member is assumed. -/
def falseAcceptance {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (truth : Ω → Bool) (pool : Finset (Ω → Bool)) (ε : ℝ≥0∞) (n : ℕ) :
    Set (Fin n → Ω) := {s | ∃ h ∈ pool, ε < error μ truth h ∧ s ∈ passes truth h n}

/-- Fixed-candidate exact probability and simultaneous pool risk control.
ENNReal thresholds are nonnegative by type; ε≤1 is explicit. n=0 is included,
as is an empty pool. This is a conditional sampling theorem, not a guarantee
that deployment really follows this distribution or that a passing h is good. -/
def SamplingCertificate : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (truth h : Ω → Bool) (n : ℕ),
    sampling μ n (passes truth h n) = (1 - error μ truth h)^n ∧
    ∀ (pool : Finset (Ω → Bool)) (ε : ℝ≥0∞), ε ≤ 1 →
      sampling μ n (falseAcceptance μ truth pool ε n) ≤
        (pool.card : ℝ≥0∞) * (1-ε)^n

/-- Four genuinely uniform points, not an opaque probability parameter. -/
noncomputable def uniformFour : Measure (Fin 4) := Measure.uniformOfFinset Finset.univ

/-- Correct on its selected point and wrong at each other point. If the point
is selected from validation itself this is an outside-pool posthoc memorizer. -/
def memorizer (seen x : Fin 4) : Bool := decide (x ≠ seen)

/-- Each single-observation posthoc memorizer passes while its actual error
is 3/4; its joint bad-pass event therefore has probability one, exceeding the
incorrectly reused singleton bound at ε=1/2. Separately, a FIXED bad candidate
passes with strictly positive probability at every finite horizon. Its bad-pass
event equals its pass event: a small joint risk need not make a passed candidate
good with high posterior probability. No conditional-measure API is required. -/
def SelectionControls : Prop :=
  IsProbabilityMeasure uniformFour ∧
  (∀ seen, error uniformFour (fun _ => false) (memorizer seen) = 3/4) ∧
  (∀ s : Fin 1 → Fin 4, s ∈ passes (fun _ => false) (memorizer (s 0)) 1) ∧
  sampling uniformFour 1
    {s | (1/2 : ℝ≥0∞) < error uniformFour (fun _ => false) (memorizer (s 0)) ∧
      s ∈ passes (fun _ => false) (memorizer (s 0)) 1} = 1 ∧
  (1 : ℝ≥0∞) > (1-1/2)^1 ∧
  (∀ n, sampling uniformFour n (passes (fun _ => false) (memorizer 0) n) =
      (1/4 : ℝ≥0∞)^n ∧
    0 < sampling uniformFour n (passes (fun _ => false) (memorizer 0) n) ∧
    {s : Fin n → Fin 4 | (1/2 : ℝ≥0∞) <
        error uniformFour (fun _ => false) (memorizer 0) ∧
      s ∈ passes (fun _ => false) (memorizer 0) n} =
      passes (fun _ => false) (memorizer 0) n)

end TruthCore.Logic.FiniteValidationLogic
