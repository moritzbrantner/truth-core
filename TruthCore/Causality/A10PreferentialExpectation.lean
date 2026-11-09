module

public import TruthCore.Causality.PossibleCauseOfContingency

/-!
A bounded analyst profile for A10's OPEN default. This is neither the source
sense's completed declaration nor probability semantics. Interpretations I,
evidence E and encountered cases X are arbitrary carriers. An epistemic
interpretation is not a metaphysically accessible world. Observation excludes
interpretations, preference selects their minimal members, and a default can
be withdrawn on new evidence. Ranking/observation calibration remains OPEN.
-/

@[expose] public section
namespace TruthCore.Causality.A10PreferentialExpectation

/-- `positive e x` records that e supports a cause for case x; it does not say
that a cause exists. `applies` tests the selected case's reference class;
`defeats` is a supplied case-specific exception policy. These semantic inputs
remain OPEN, as do the evidential meaning of observations and the preference
relation. No structural causal law, PSR or numerical probability is assumed. -/
structure Profile (I E X : Type) where
  observed : E → Prop
  satisfies : I → E → Prop
  preferred : I → I → Prop
  positive : E → X → Prop
  applies : X → Prop
  defeats : E → X → Prop
  hasCause : I → X → Prop

/-- Agreement with all currently observed evidence. -/
def Admissible (p : Profile I E X) (i : I) : Prop :=
  ∀ e, p.observed e → p.satisfies i e

/-- Undominated admissible interpretations. Existence is NOT automatic,
even on a nonempty carrier: evidence may be inconsistent or preference cyclic. -/
def Best (p : Profile I E X) (i : I) : Prop :=
  Admissible p i ∧ ∀ j, Admissible p j → ¬ p.preferred j i

/-- Positive observed support, explicit applicability, no observed defeater,
a nonempty best class, and agreement of every best interpretation on causation
of this SAME case. Includes nonvacuity rather than vacuous skeptical warrant. -/
def Expect (p : Profile I E X) (x : X) : Prop :=
  (∃ e, p.observed e ∧ p.positive e x) ∧ p.applies x ∧
  (∀ e, p.observed e → ¬ p.defeats e x) ∧
  (∃ i, Best p i) ∧ ∀ i, Best p i → p.hasCause i x

/-- Consequential observed exceptions defeat the profile even if all preferred
interpretations continue to report a cause. -/
theorem defeated (p : Profile I E X) (x : X) (e : E)
    (ho : p.observed e) (hd : p.defeats e x) : ¬ Expect p x := by
  intro h
  exact h.2.2.1 e ho hd

/-- This yields an epistemic interpretation only; no truth or Dia follows. -/
theorem supportedInterpretation (p : Profile I E X) (x : X)
    (h : Expect p x) : ∃ i, Best p i ∧ p.hasCause i x := by
  obtain ⟨i, hi⟩ := h.2.2.2.1
  exact ⟨i, hi, h.2.2.2.2 i hi⟩

/-- The independent realization bridge retains the same selected x. Q must
supply its own causal meaning, same-bearer and actualist guards; a report is
not equated with exercise. It is sufficient to realize ONE best caused case,
not every interpretation. This is a conditional sufficient bundle, not a
claim of globally weakest metaphysical conditions. -/
theorem possibleFromBridge (p : Profile I E X) (x : X)
    (access : W → W → Prop) (w : W) (Q : W → X → Prop)
    (h : Expect p x)
    (bridge : ∀ i, Best p i → p.hasCause i x →
      ∃ v, access w v ∧ Q v x) : ∃ v, access w v ∧ Q v x := by
  obtain ⟨i, hi, hc⟩ := supportedInterpretation p x h
  exact bridge i hi hc

/-- A deliberately stronger totality bridge connects to the EXISTING Scenario
route. It carries beginning, actual concrete source and outside-all-contingents
conditions in PossiblyExternallyCausedAt explicitly; an individual prior
partial cause does not suffice. No guard is inferred from default warrant. -/
theorem scenarioFromBridge (p : Profile I E X) (x : X)
    (s : PossibleCauseOfContingency.Scenario W B) (w : W)
    (h : Expect p x)
    (bridge : ∀ i, Best p i → p.hasCause i x →
      PossibleCauseOfContingency.PossiblyExternallyCausedAt s w)
    (frame : PossibleCauseOfContingency.UniversalFrame s) :
    PossibleCauseOfContingency.NecessaryConcreteAt s w := by
  obtain ⟨i, hi, hc⟩ := supportedInterpretation p x h
  exact PossibleCauseOfContingency.possibleExternalCauseYieldsNecessary
    s w frame (bridge i hi hc)

/-- Finite fixtures only. The initial observation false leaves both interpretations admissible;
observing true excludes the preferred caused interpretation false. -/
def fixture (updated : Bool) : Profile Bool Bool Bool where
  observed := fun e => e = false ∨ updated = true ∧ e = true
  satisfies := fun i e => e = false ∨ i = true
  preferred := fun j i => j = false ∧ i = true
  positive := fun e _ => e = false
  applies := fun x => x = false
  defeats := fun _ _ => False
  hasCause := fun i _ => i = false

/-- Nonvacuity: a positively supported applicable selected case. -/
theorem fixtureExpected : Expect (fixture false) false := by
  simp [Expect, Best, Admissible, fixture]

/-- Evidence extension withdraws warrant without changing cause interpretation,
preference, reference class, or declaring the new evidence an explicit defeater. -/
theorem fixtureWithdrawal : ¬ Expect (fixture true) false := by
  simp [Expect, Best, Admissible, fixture, Bool.forall_bool]

/-- Selection does not entail reference-class membership; true is out of scope,
though its epistemic cause predicate is identical to the accepted case's. -/
theorem selectedNotSampled : ¬ Expect (fixture false) true := by
  simp [Expect, Best, Admissible, fixture]

/-- Bridge omission: full default warrant coexists with the EXISTING brute-only
Scenario's lack of possible external cause and necessary concrete individual. -/
theorem noObjectiveTransfer : Expect (fixture false) false ∧
    ¬ PossibleCauseOfContingency.PossiblyExternallyCausedAt
      PossibleCauseOfContingency.bruteOnly false ∧
    ¬ PossibleCauseOfContingency.NecessaryConcreteAt
      PossibleCauseOfContingency.bruteOnly false :=
  ⟨fixtureExpected, PossibleCauseOfContingency.bruteOnlyNoExternalCause,
    PossibleCauseOfContingency.bruteOnlyNoNecessary⟩

/-- Positive evidence is substantive: merely deleting it removes expectation,
even though observation, preference and cause reports remain unchanged. -/
theorem noPositiveSupport :
    ¬ Expect { fixture false with positive := fun _ _ => False } false := by
  simp [Expect]

/-- Applicability and an epistemic consensus do not neutralize a defeater. -/
theorem observedDefeater :
    ¬ Expect { fixture false with defeats := fun e _ => e = false } false := by
  exact defeated _ false false (Or.inl rfl) rfl

/-- Nonvacuity is independent: cyclic preference leaves no best interpretation,
even though observations are consistent and every interpretation says caused. -/
theorem noBest : ¬ Expect { fixture false with
    preferred := fun _ _ => True, hasCause := fun _ _ => True } false := by
  intro h
  obtain ⟨i, hi⟩ := h.2.2.2.1
  exact hi.2 i hi.1 trivial

/-- A full bridge-bearing bundle is satisfiable in the existing mixed Scenario.
This reuses its guarded external totality cause, not a new physical model. -/
theorem bridgeBundleNonvacuous : Expect (fixture false) false ∧
    (∀ i, Best (fixture false) i → (fixture false).hasCause i false →
      PossibleCauseOfContingency.PossiblyExternallyCausedAt
        PossibleCauseOfContingency.mixed false) ∧
    PossibleCauseOfContingency.UniversalFrame
      PossibleCauseOfContingency.mixed :=
  ⟨fixtureExpected, (fun _ _ _ =>
    PossibleCauseOfContingency.mixedPossibleExternalCause),
    PossibleCauseOfContingency.mixedUniversal⟩

end TruthCore.Causality.A10PreferentialExpectation
