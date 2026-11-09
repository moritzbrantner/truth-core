module
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Analyst finite sampling model for #418; attribution deferred. The three
cells are fine-tuned observer worlds, other observer worlds, and unobserved
worlds. These are stipulated mutually exclusive cells, not empirical estimates.
Natural models may represent observer-weighted multiverse sampling; no uniform
sampling over universes or designer preference is built into the definition. -/
@[expose] public section
namespace TruthCore.Science.FineTuningSelection

/-- A normalized finite probability distribution, using Mathlib finite sums.
The interpretation of these cells as physical evidence remains OPEN. -/
structure Sampling where
  weight : Fin 3 → ℚ
  nonnegative : ∀ i, 0 ≤ weight i
  normalized : ∑ i, weight i = 1
  observers_pos : 0 < weight 0 + weight 1
  evidence_pos : 0 < weight 0

/-- P(fine evidence | observer) by the finite event-ratio formula. -/
def likelihood (s : Sampling) : ℚ := s.weight 0 / (s.weight 0 + s.weight 1)

def factor (d n : Sampling) : ℚ := likelihood d / likelihood n

/-- Explicit calibration, stronger than simply observing fine-tuning. -/
def Calibrated (d n : Sampling) : Prop :=
  3/4 ≤ likelihood d ∧ likelihood n ≤ 1/4

def CalibrationDirection : Prop := ∀ d n : Sampling,
  Calibrated d n → 1 < factor d n

/-- The cells have positive observer and fine evidence mass in every model. -/
def design : Sampling where
  weight := ![3/8, 1/8, 1/2]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  observers_pos := by norm_num
  evidence_pos := by norm_num

def natural : Sampling where
  weight := ![1/8, 3/8, 1/2]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  observers_pos := by norm_num
  evidence_pos := by norm_num

/-- Same unconditional fine-evidence mass as natural, but observers occur
only in that cell. Selection makes its conditional likelihood one. -/
def selectedNatural : Sampling where
  weight := ![1/8, 0, 7/8]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  observers_pos := by norm_num
  evidence_pos := by norm_num

/-- Retain natural's calibration and reverse only designer preference. -/
def indifferentDesigner : Sampling where
  weight := ![1/16, 7/16, 1/2]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  observers_pos := by norm_num
  evidence_pos := by norm_num

def SelectionControls : Prop :=
  Calibrated design natural ∧ factor design natural = 3 ∧
  natural.weight 0 = selectedNatural.weight 0 ∧
  likelihood natural = 1/4 ∧ likelihood selectedNatural = 1 ∧
  factor design selectedNatural = 3/4 ∧
  likelihood natural ≤ 1/4 ∧ factor indifferentDesigner natural = 1/2 ∧
  (1/10 : ℚ) * factor design natural < 1

end TruthCore.Science.FineTuningSelection
