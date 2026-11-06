module

public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Finset.Lattice.Fold

/-! Analyst probability-to-qualitative-belief reconstruction for #1063;
attribution deferred. Events are actual Mathlib sets in finite measurable spaces,
and μ is an actual Mathlib measure. The theorems explicitly require normalization.
A threshold policy selects events as full beliefs. Selection is not a predicate
for pro tanto reasons, categorical obligation, knowledge, or actual truth. -/

@[expose] public section
namespace TruthCore.Logic.ThresholdBelief
open MeasureTheory Set
open scoped ENNReal

/-- A declared full-belief policy; whether this licenses rational belief is an
OPEN philosophical bridge. The real-valued probability is Mathlib Measure.real. -/
def Accepted {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (t : ℝ)
    (A : Set Ω) : Prop := t ≤ μ.real A

/-- Binary conjunction closure. Normalization and t≤1 separately provide
acceptance of the empty conjunction (the universal event). -/
def ConjunctionClosed {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (t : ℝ) : Prop :=
  ∀ A B : Set Ω, Accepted μ t A → Accepted μ t B → Accepted μ t (A ∩ B)

/-- Points too probable to be omitted by any threshold-accepted event. This is
not an actual-world selector or an assertion that high probability is truth. -/
def HeavyCore {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (t : ℝ) : Set Ω :=
  {x | 1-t < μ.real {x}}

/-- The finite threshold core is exactly the intersection of all accepted events.
Conjunction closure is equivalent to acceptance of this core. Numerical guards
also ensure that the universal event is accepted and the empty event rejected. -/
def CoreBoundary : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ), 0<t → t≤1 →
    (∀ x, x ∈ HeavyCore μ t ↔ ∀ A, Accepted μ t A → x ∈ A) ∧
    (ConjunctionClosed μ t ↔ Accepted μ t (HeavyCore μ t)) ∧
    Accepted μ t univ ∧ ¬ Accepted μ t ∅

/-- Actual uniform counting-conditioned measure, including the zero measure at
N=0. Every substantive uniform theorem explicitly assumes N>0. -/
noncomputable def uniform (N : ℕ) : Measure (Fin N) :=
  ProbabilityTheory.uniformOn univ

/-- Exact finite-uniform boundary and failure for every fixed subcertainty
threshold. A context-dependent threshold is a different policy. -/
def UniformBoundary : Prop :=
  (∀ N : ℕ, 0<N → ∀ t : ℝ, 0<t → t≤1 →
    (ConjunctionClosed (uniform N) t ↔ 1-1/(N:ℝ)<t)) ∧
  (∀ t : ℝ, 0<t → t<1 → ∃ N : ℕ, 2≤N ∧
    ¬ ConjunctionClosed (uniform N) t ∧
    (∀ i : Fin N, Accepted (uniform N) t {i}ᶜ) ∧
    (⋂ i : Fin N, ({i}ᶜ : Set (Fin N))) = ∅)

/-- A finite union-bound consequence: no independence is assumed. This only
bounds the support of the conjunction, not its actual truth or warrant. The
threshold-one control is finite, not a probability-one-to-necessity principle. -/
def SupportBoundary : Prop :=
  (∀ (Ω : Type) [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Type) [Fintype I]
    (A : I → Set Ω),
    1 ≤ μ.real (⋂ i, A i) + ∑ i, (1-μ.real (A i))) ∧
  (∀ (Ω : Type) [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ], ConjunctionClosed μ 1)

/-- A nontrivial coherent threshold profile: true has probability 19/20 and
false 1/20. Actuality can be false without changing this supplied measure. -/
noncomputable def skew : Measure Bool :=
  (19/20 : ℝ≥0∞) • Measure.dirac true + (1/20 : ℝ≥0∞) • Measure.dirac false

/-- A proper contingent event can be accepted by a conjunction-closed,
consistent policy yet fail at a positive-probability actual alternative. -/
def SkewSurvivor : Prop :=
  IsProbabilityMeasure skew ∧
  skew.real {true} = 19/20 ∧ skew.real {false} = 1/20 ∧
  ConjunctionClosed skew (9/10) ∧ Accepted skew (9/10) {true} ∧
  ¬ Accepted skew (9/10) ∅ ∧
  0 < skew.real {false} ∧ (false ∉ ({true} : Set Bool))

end TruthCore.Logic.ThresholdBelief
