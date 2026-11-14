module

public import TruthCore.Logic.ThresholdBelief
public import TruthCore.Logic.ReflectiveCoherence
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability

/-! Analyst formulation for #1584 (preface paradox; connection plan #930/#931/#934),
attribution deferred: Makinson 1965 and Bovens–Olsson 2000 are navigation leads,
not sourced claims.

A finite *assertion-error profile* has one shared coordinate (a common-mode
condition every assertion relies on) and `n` local coordinates drawn by the
genuine Mathlib product of the SAME local measure, independent of the shared one.
Assertion `i` is true exactly when the shared condition `G` and its own local
condition `C` hold. Local checks raise a flag in a stipulated local event `F`.

This is a stipulated comparison model, not a model of the Truth Core corpus or
of any actual belief system. It assigns no probability to any corpus statement.
`ν C = 1` is the shared-dependence control; `G = univ` (or `κ G = 1`) is the
isolated independent-error control. Threshold acceptance reuses
`ThresholdBelief.Accepted`, an analyst policy, not epistemic warrant.
-/

@[expose] public section
namespace TruthCore.Logic.PrefaceConnectivity
open MeasureTheory ProbabilityTheory Set
open TruthCore.Logic.ThresholdBelief (Accepted)
open TruthCore.Logic.ReflectiveCoherence
open scoped ENNReal

/-- Shared coordinate measure `κ` times the independent product of `n` copies of
the local measure `ν`. Independence of the local coordinates from each other and
from the shared coordinate is stipulated by this product construction. -/
noncomputable def profile {Γ Λ : Type} [MeasurableSpace Γ] [MeasurableSpace Λ]
    (κ : Measure Γ) (ν : Measure Λ) (n : ℕ) : Measure (Γ × (Fin n → Λ)) :=
  κ.prod (Measure.pi fun _ => ν)

/-- Assertion `i` is true: the shared condition and its own local condition hold. -/
def assertion {Γ Λ : Type} {n : ℕ} (G : Set Γ) (C : Set Λ) (i : Fin n) :
    Set (Γ × (Fin n → Λ)) := {x | x.1 ∈ G ∧ x.2 i ∈ C}

/-- Every one of the `n` assertions is true. -/
def allTrue {Γ Λ : Type} (G : Set Γ) (C : Set Λ) (n : ℕ) : Set (Γ × (Fin n → Λ)) :=
  ⋂ i, assertion G C i

/-- At least one of the `n` assertions is false (the preface's higher-order content). -/
def someFalse {Γ Λ : Type} (G : Set Γ) (C : Set Λ) (n : ℕ) : Set (Γ × (Fin n → Λ)) :=
  ⋃ i, (assertion G C i)ᶜ

/-- No local check raised a flag. The checks see only local coordinates: they are
blind to the shared condition by construction. -/
def noFlag {Γ Λ : Type} (F : Set Λ) (n : ℕ) : Set (Γ × (Fin n → Λ)) :=
  {x | ∀ i, x.2 i ∉ F}

/-- ERROR_DEPENDENCE_1, shared-only dependence: every assertion expresses the shared
condition (its local condition is almost sure). Errors are then fully common-mode. -/
def SharedOnly {Λ : Type} [MeasurableSpace Λ] (ν : Measure Λ) (C : Set Λ) : Prop :=
  ν C = 1

/-- ERROR_DEPENDENCE_2, isolated errors only: the shared condition is almost sure,
so the assertions fail only through the independent local coordinates. -/
def IsolatedOnly {Γ : Type} [MeasurableSpace Γ] (κ : Measure Γ) (G : Set Γ) : Prop :=
  κ G = 1

/-- ERROR_DEPENDENCE_3, a truth-independent (non-discriminating) check: absence of a
flag is probabilistically independent of local correctness. A check that only
re-derives the assertion from the same untested input is one way to have this. -/
def TruthIndependentFlag {Λ : Type} [MeasurableSpace Λ] (ν : Measure Λ) (C F : Set Λ) :
    Prop :=
  ν (C ∩ Fᶜ) = ν C * ν Fᶜ

/-- Perfect local detection: the flag fires exactly on local error. It is still
blind to failure of the shared condition. -/
def PerfectLocalDetection {Λ : Type} (C F : Set Λ) : Prop := F = Cᶜ

/-- Exact event probabilities of the profile (`0<n`): each assertion has `κ G * ν C`,
all together `κ G * (ν C)^n`, some failure the complement; with checks, the
no-flag event has `ν Fᶜ ^ n` and all-true-without-flag `κ G * ν (C ∩ Fᶜ) ^ n`. -/
def ProfileProbabilities : Prop :=
  ∀ (Γ Λ : Type) [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [Fintype Λ] [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ]
    (κ : Measure Γ) [IsProbabilityMeasure κ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C F : Set Λ) (n : ℕ), 0 < n →
    (∀ i : Fin n, profile κ ν n (assertion G C i) = κ G * ν C) ∧
    profile κ ν n (allTrue G C n) = κ G * ν C ^ n ∧
    profile κ ν n (someFalse G C n) = 1 - κ G * ν C ^ n ∧
    profile κ ν n (noFlag F n) = ν Fᶜ ^ n ∧
    profile κ ν n (allTrue G C n ∩ noFlag F n) = κ G * ν (C ∩ Fᶜ) ^ n

/-- Per-assertion probabilities do not fix the joint probability (tests 1–2 of
#1584). With the same per-assertion value `q` strictly between 0 and 1 and `n≥2`
assertions, the shared-dependence profile (every assertion expresses the same
`G`, `ν C = 1`) gives joint `q` and some-failure `1-q`, while the isolated
independent-error profile (`κ G = 1`) gives `q^n < q`. Conditioning on `n≥1`
repetitions of one evidence event equals conditioning on it once. -/
def MarginalsUnderdetermineJoint : Prop :=
  (∀ (Γ Λ : Type) [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [Fintype Λ] [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ]
    (κ : Measure Γ) [IsProbabilityMeasure κ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C : Set Λ) (q : ℝ≥0∞) (n : ℕ), 0 < q → q < 1 → 2 ≤ n →
    -- shared dependence: local conditions always hold
    (κ G = q → SharedOnly ν C →
      (∀ i : Fin n, profile κ ν n (assertion G C i) = q) ∧
      profile κ ν n (allTrue G C n) = q ∧ profile κ ν n (someFalse G C n) = 1 - q) ∧
    -- isolated independent errors: shared condition always holds
    (IsolatedOnly κ G → ν C = q →
      (∀ i : Fin n, profile κ ν n (assertion G C i) = q) ∧
      profile κ ν n (allTrue G C n) = q ^ n ∧ q ^ n < q))
  ∧ ∀ (Ω ι : Type) [MeasurableSpace Ω] [Nonempty ι] (μ : Measure Ω) (E : Set Ω),
      μ[|⋂ _i : ι, E] = μ[|E]

/-- Makinson boundary in the profile (test 5 of #1584). For a threshold above
one half, pure shared dependence never jointly accepts an assertion and the
higher-order some-failure event, at any `n`. With any local error (`ν C < 1`),
every threshold below one accepts the some-failure event for all sufficiently
large `n`, while acceptance of each assertion depends only on `κ G * ν C`, not
on `n`: dependence on the shared condition does not remove the tension. -/
def HierarchicalPrefaceBoundary : Prop :=
  ∀ (Γ Λ : Type) [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [Fintype Λ] [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ]
    (κ : Measure Γ) [IsProbabilityMeasure κ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C : Set Λ),
    (SharedOnly ν C → ∀ (t : ℝ), 1/2 < t → ∀ n (i : Fin n),
      ¬ (Accepted (profile κ ν n) t (assertion G C i) ∧
         Accepted (profile κ ν n) t (someFalse G C n))) ∧
    (ν C < 1 → ∀ (t : ℝ), t < 1 → ∃ N, ∀ n, N ≤ n →
      Accepted (profile κ ν n) t (someFalse G C n) ∧
      ∀ i : Fin n, (Accepted (profile κ ν n) t (assertion G C i) ↔
        t ≤ (κ G * ν C).toReal))

/-- Local cross-checks (test 3 of #1584), conditioning on no flag (`0<n`):
the posterior that all assertions are true is `κ G * (ν (C ∩ Fᶜ) / ν Fᶜ)^n`,
hence never above `κ G`: no number of shared-blind local checks raises joint
support above the shared condition's probability. The conditioned probability of
the shared condition itself stays exactly `κ G`. Flags here are shared-blind by
construction; checks sensitive to the shared condition are outside this model.
If the flag fires exactly on
local error (`F = Cᶜ`), the posterior of all-true is `κ G` and of some-failure
`1 - κ G` for every `n`: only the shared risk remains. Each conditioned
assertion has `κ G * (ν (C ∩ Fᶜ) / ν Fᶜ)`, so after perfect checks no threshold
above one half accepts both an assertion and the some-failure event.
If the flag is probabilistically independent of local correctness, conditioning
on no flag leaves the all-true probability unchanged. -/
def CrossCheckBoundary : Prop :=
  ∀ (Γ Λ : Type) [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [Fintype Λ] [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ]
    (κ : Measure Γ) [IsProbabilityMeasure κ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C F : Set Λ) (n : ℕ), 0 < n → ν Fᶜ ≠ 0 →
    (profile κ ν n)[|noFlag F n] (allTrue G C n) = κ G * (ν (C ∩ Fᶜ) / ν Fᶜ) ^ n ∧
    (profile κ ν n)[|noFlag F n] (allTrue G C n) ≤ κ G ∧
    (profile κ ν n)[|noFlag F n] {x | x.1 ∈ G} = κ G ∧
    (∀ i : Fin n, (profile κ ν n)[|noFlag F n] (assertion G C i) =
      κ G * (ν (C ∩ Fᶜ) / ν Fᶜ)) ∧
    (PerfectLocalDetection C F →
      (profile κ ν n)[|noFlag F n] (allTrue G C n) = κ G ∧
      (profile κ ν n)[|noFlag F n] (someFalse G C n) = 1 - κ G ∧
      ∀ (t : ℝ), 1/2 < t → ∀ i : Fin n,
        ¬ (Accepted ((profile κ ν n)[|noFlag F n]) t (assertion G C i) ∧
           Accepted ((profile κ ν n)[|noFlag F n]) t (someFalse G C n))) ∧
    (TruthIndependentFlag ν C F →
      (profile κ ν n)[|noFlag F n] (allTrue G C n) = profile κ ν n (allTrue G C n))

/-- Worldview elimination (test 4 of #1584), reusing `ReflectiveCoherence`. An
inconsistent bundle is false at every world. With the explicit coverage premise
that some candidate is true at `actual`, eliminating all other candidates by
inconsistency makes the survivor true there. Without coverage the inference
fails: the two-world control has an inconsistent rival and a consistent
survivor that is false at the actual world. -/
def EliminationCoverage : Prop :=
  (∀ (World Claim : Type) (S : Semantics World Claim) (W : Worldview Claim),
    ¬ Consistent S W → ∀ w, ¬ Models S W w) ∧
  (∀ (World Claim ι : Type) (S : Semantics World Claim) (W : ι → Worldview Claim)
    (actual : World) (k : ι),
    (∃ j, Models S (W j) actual) → (∀ j, j ≠ k → ¬ Consistent S (W j)) →
      Models S (W k) actual) ∧
  (∃ (W : Bool → Worldview Bool),
    ¬ Consistent twoWorldSemantics (W false) ∧
    Consistent twoWorldSemantics (W true) ∧
    ¬ Models twoWorldSemantics (W true) true ∧
    ¬ ∃ j, Models twoWorldSemantics (W j) true)

end TruthCore.Logic.PrefaceConnectivity
