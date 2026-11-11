module
public import TruthCore.Science.FineTuningSelection
public import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
@[expose] public section
namespace TruthCore.Science.FineTuningEvidence
open FineTuningSelection MeasureTheory

def raw (d n : Sampling) : ℚ := d.weight 0 / n.weight 0
def observer (d n : Sampling) : ℚ :=
  (d.weight 0 + d.weight 1) / (n.weight 0 + n.weight 1)

def Factorization : Prop := ∀ d n : Sampling,
  factor d n = raw d n / observer d n ∧
  (1 < factor d n ↔ observer d n < raw d n) ∧
  (factor d n = 1 ↔ raw d n = observer d n) ∧
  (d.weight 1 = 0 → n.weight 1 = 0 → factor d n = 1)

def screenedDesign : Sampling where
  weight := ![1/2, 0, 1/2]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  observers_pos := by norm_num
  evidence_pos := by norm_num

def screenedNatural : Sampling where
  weight := ![1/10, 0, 9/10]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  observers_pos := by norm_num
  evidence_pos := by norm_num

def Controls : Prop :=
  raw design natural = 3 ∧ observer design natural = 1 ∧ factor design natural = 3 ∧
  raw design selectedNatural = 3 ∧ observer design selectedNatural = 4 ∧
  factor design selectedNatural = 3/4 ∧
  raw screenedDesign screenedNatural = 5 ∧ observer screenedDesign screenedNatural = 5 ∧
  factor screenedDesign screenedNatural = 1

/-- ENNReal event ratios; evidential use requires finite positive denominators.
The invariance identity itself holds for all measures, including degenerate ones. -/
noncomputable def eventFactor {X : Type*} [MeasurableSpace X] (d n : Measure X) (e : Set X) :=
  d e / n e

noncomputable def conditionalFactor {X : Type*} [MeasurableSpace X]
    (d n : Measure X) (e o : Set X) :=
  (d (e ∩ o) / d o) / (n (e ∩ o) / n o)

/-- Genuine measurable bijections, not finite permutations or replacement priors. -/
def PushforwardInvariance : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y]
    (f : X ≃ᵐ Y) (d n : Measure X) (e o : Set X),
    (d.map f) (f '' e) = d e ∧ (n.map f) (f '' e) = n e ∧
    eventFactor (d.map f) (n.map f) (f '' e) = eventFactor d n e ∧
    conditionalFactor (d.map f) (n.map f) (f '' e) (f '' o) =
      conditionalFactor d n e o
end TruthCore.Science.FineTuningEvidence
