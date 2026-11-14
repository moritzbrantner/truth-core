module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.UniformOn

/-! Analyst formulation for #1586 (Enoch's third-factor reply to Street's
Darwinian dilemma), attribution deferred: the existing claim
`ENOCH-THIRD-FACTOR-ACCESS-REPLY` (Enoch 2010, §§5.1–5.3) records Enoch's
qualified, non-quantitative proposal. No probability, error rate or
distribution below is attributed to Enoch or Street.

One common distribution `μ` of cases is fixed. On each case `ω`:

* `B ω` is the selected-for evaluative judgment (for example "this act is to be
  done");
* `F ω` is the third factor, specified independently of `B` and `M`: whether the
  act promotes the survival/reproductive goods that selection responded to;
* `M ω` is the matching normative truth about the same act, under the same
  verdict type as `B` (pro tanto, all-things-considered, impartial, …).

`disagree B F` is the selection error set and `disagree F M` the factor/truth
gap. The union bound below needs no independence: it rests on the inclusion
`{B ≠ M} ⊆ {B ≠ F} ∪ {F ≠ M}`. The rates `e₁`, `e₂` are inputs. Their empirical
and normative calibration is open: the premise that survival is pro tanto good
does not bound `e₂` for categorical, impartial or all-things-considered verdicts.
The finite models on `Fin 4` are stipulated comparison models; their truth
values are not claims about actual moral truths.
-/

@[expose] public section
namespace TruthCore.Logic.ThirdFactorTracking
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The cases in which two assignments differ. -/
def disagree {Ω V : Type} (X Y : Ω → V) : Set Ω := {ω | X ω ≠ Y ω}

/-- The cases in which two assignments coincide. -/
def agree {Ω V : Type} (X Y : Ω → V) : Set Ω := {ω | X ω = Y ω}

/-- OPEN input: on the common distribution `μ`, the selected-for judgment `B`
differs from the third factor `F` in a set of cases of measure at most `e₁`. -/
def SelectionErrorAtMost {Ω V : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (B F : Ω → V) (e₁ : ℝ≥0∞) : Prop :=
  μ (disagree B F) ≤ e₁

/-- OPEN input: on the same distribution, the third factor `F` differs from the
matching normative truth `M` in a set of cases of measure at most `e₂`. -/
def FactorTruthGapAtMost {Ω V : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (F M : Ω → V) (e₂ : ℝ≥0∞) : Prop :=
  μ (disagree F M) ≤ e₂

/-- The judgment `B` differs from the truth `M` in a set of cases of measure at
most `e`; and, if `μ` is a probability measure and the agreement event is
measurable, `B` agrees with `M` with probability at least `1 - e` (truncated
subtraction: vacuous once `e ≥ 1`). -/
def JudgmentTruthAgreementAtLeast {Ω V : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (B M : Ω → V) (e : ℝ≥0∞) : Prop :=
  μ (disagree B M) ≤ e ∧
    (IsProbabilityMeasure μ → MeasurableSet (agree B M) → 1 - e ≤ μ (agree B M))

/-- Exact binary error accounting (sharpness). For binary verdicts the
judgment/truth error set is the symmetric difference of the two error sets,
because two errors cancel. So the judgment/truth error equals the sum of the
two error rates minus twice their joint error, and, for a finite measure, it
attains that sum exactly when the joint error is null. -/
def BinaryErrorAccounting : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (B F M : Ω → Bool),
    MeasurableSet (disagree B F) → MeasurableSet (disagree F M) →
    disagree B M = symmDiff (disagree B F) (disagree F M) ∧
    μ (disagree B M) + 2 * μ (disagree B F ∩ disagree F M) =
      μ (disagree B F) + μ (disagree F M) ∧
    (IsFiniteMeasure μ →
      (μ (disagree B M) = μ (disagree B F) + μ (disagree F M) ↔
        μ (disagree B F ∩ disagree F M) = 0))

/-- An aggregate gap does not bound a subclass gap beyond dilution: conditioning
on a measurable class `S` of cases (for example impartial hard cases) gives a
factor/truth gap of at most the aggregate gap divided by the class weight. -/
def SubclassGapBound : Prop :=
  ∀ (Ω V : Type) [MeasurableSpace Ω] (μ : Measure Ω) (F M : Ω → V) (S : Set Ω),
    MeasurableSet S → μ[disagree F M | S] ≤ μ (disagree F M) / μ S

/-- Four equally weighted stipulated cases. -/
noncomputable def cases4 : Measure (Fin 4) := ProbabilityTheory.uniformOn univ

/-- Case `3` stands in for an impartial/hard case (costly help to a stranger,
or restraint toward an outgroup rival when harming would pay); cases `0`–`2`
for adaptive/self-regarding cases (care for one's own offspring, avoiding
injury). The labels are interpretive placeholders. -/
def hardCase : Set (Fin 4) := {3}

/-- The factor endorses every act: each act promotes the selected-for goods. -/
def factorAll : Fin 4 → Bool := fun _ => true

/-- Stipulated truth agreeing with the factor except in the hard case. -/
def truthHard : Fin 4 → Bool := fun ω => decide (ω ≠ 3)

/-- A judgment wrong only in case `0`. -/
def judgmentOff0 : Fin 4 → Bool := fun ω => decide (ω ≠ 0)

/-- A truth differing from the factor only in case `1`. -/
def truthOff1 : Fin 4 → Bool := fun ω => decide (ω ≠ 1)

/-- Finite models. (1) Sharpness: selection error `1/4` (case 0) and
factor/truth gap `1/4` (case 1) in disjoint cases give agreement exactly
`1/2 = 1 - (1/4 + 1/4)`. (2) Cancellation: the same two error rates on the same
case give agreement `1`, so the bound is not attained when binary errors
coincide. (3) Hard-case concentration: with judgment equal to the factor
(`e₁ = 0`) and a gap `1/4` located in the hard case, aggregate agreement is
`3/4`, the bound attained, while agreement conditioned on the hard case is `0`
and on the adaptive cases `1`; the conditioned gap `1` attains the subclass
bound `(1/4)/(1/4)`. -/
def ThirdFactorModels : Prop :=
  IsProbabilityMeasure cases4 ∧
  (cases4 (disagree judgmentOff0 factorAll) = 1/4 ∧
    cases4 (disagree factorAll truthOff1) = 1/4 ∧
    cases4 (agree judgmentOff0 truthOff1) = 1/2) ∧
  (cases4 (disagree judgmentOff0 factorAll) = 1/4 ∧
    cases4 (disagree factorAll judgmentOff0) = 1/4 ∧
    cases4 (agree judgmentOff0 judgmentOff0) = 1) ∧
  (cases4 (disagree factorAll factorAll) = 0 ∧
    cases4 (disagree factorAll truthHard) = 1/4 ∧
    cases4 (agree factorAll truthHard) = 3/4 ∧
    cases4[agree factorAll truthHard | hardCase] = 0 ∧
    cases4[agree factorAll truthHard | hardCaseᶜ] = 1 ∧
    cases4[disagree factorAll truthHard | hardCase] = 1 ∧
    cases4 (disagree factorAll truthHard) / cases4 hardCase = 1)

end TruthCore.Logic.ThirdFactorTracking
