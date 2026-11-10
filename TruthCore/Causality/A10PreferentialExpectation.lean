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

/-- Unindexed composition with the EXISTING Scenario route. It carries NO A10
content: the bridge consequent `PossiblyExternallyCausedAt s w` mentions neither
the interpretation `i` nor the case `x`, the case carrier is unrelated to the
Scenario's beings, and the totality cause exists at an accessible history, not
at `w`. The theorem merely rewraps the existing Scenario antecedent; any proof
of that antecedent satisfies the bridge (`bridgeBundleNonvacuous`). The
same-case version is `sameCaseNecessarySource` / `sameCaseScenario` below. -/
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

/-- The unindexed bridge bundle is satisfiable in the existing mixed Scenario,
but only by a CONSTANT bridge reusing `mixedPossibleExternalCause`: this
witnesses that the old bridge ignores the A10 data, not a same-case link. -/
theorem bridgeBundleNonvacuous : Expect (fixture false) false ∧
    (∀ i, Best (fixture false) i → (fixture false).hasCause i false →
      PossibleCauseOfContingency.PossiblyExternallyCausedAt
        PossibleCauseOfContingency.mixed false) ∧
    PossibleCauseOfContingency.UniversalFrame
      PossibleCauseOfContingency.mixed :=
  ⟨fixtureExpected, (fun _ _ _ =>
    PossibleCauseOfContingency.mixedPossibleExternalCause),
    PossibleCauseOfContingency.mixedUniversal⟩

/-! ### Same-case realization bridge

`scenarioFromBridge` above carries NO A10 content: its bridge consequent
`PossiblyExternallyCausedAt s w` mentions neither the interpretation nor the
case, so it merely rewraps the existing Scenario antecedent, and a constant
proof of that antecedent satisfies it (`bridgeBundleNonvacuous`). The
same-case version below adds an explicit dictionary `src : I → X → B` naming
the Scenario bearer that interpretation `i` reports as the cause of case `x`,
and requires the guarded totality cause in an accessible history to be THAT
bearer. The dictionary is an OPEN analyst input: nothing in A10's default
fixes it, and its adequacy (that the report really is about this bearer) is
not proved. -/

/-- The dictionary-named bearer `c` is, in some history accessible from `w`,
an existing concrete cause of the beginning contingent totality and outside all
its members. The cause exists at the accessible history `v`, not (by this
predicate) at `w`. -/
def TotalityCauseVia (s : PossibleCauseOfContingency.Scenario W B) (w : W)
    (c : B) : Prop :=
  ∃ v, s.ontic.frame.access w v ∧
    PossibleCauseOfContingency.ContingencyBeginsAt s v ∧
    s.concrete c ∧ s.ontic.ExistsAt v c ∧ s.causesContingencyTotality v c ∧
    PossibleCauseOfContingency.OutsideContingentTotalityAt s v c

/-- Same-case realization bridge: every best interpretation that reports a
cause of THIS case `x` has its dictionary-named cause `src i x` realized as a
guarded totality cause in an accessible history. -/
def SameCaseBridge (p : Profile I E X)
    (s : PossibleCauseOfContingency.Scenario W B) (w : W)
    (src : I → X → B) (x : X) : Prop :=
  ∀ i, Best p i → p.hasCause i x → TotalityCauseVia s w (src i x)

/-- A dictionary-named realized cause yields the OLD unindexed antecedent;
the converse fails (`dictionaryLoadBearing`). -/
theorem totalityCauseViaPossible (s : PossibleCauseOfContingency.Scenario W B)
    (w : W) (c : B) (h : TotalityCauseVia s w c) :
    PossibleCauseOfContingency.PossiblyExternallyCausedAt s w := by
  obtain ⟨v, hv, hb, hc, he, hcause, ho⟩ := h
  exact ⟨v, hv, hb, c, hc, he, hcause, ho⟩

/-- Under universal accessibility, a realized dictionary-named bearer is itself
an actually existing, necessarily existing concrete individual at `w`. -/
theorem totalityCauseViaNecessary (s : PossibleCauseOfContingency.Scenario W B)
    (w : W) (c : B) (frame : PossibleCauseOfContingency.UniversalFrame s)
    (h : TotalityCauseVia s w c) :
    s.concrete c ∧ s.ontic.ExistsAt w c ∧
      TruthCore.German.Kant.CosmologicalInference.NecessaryAt s.ontic w c := by
  classical
  obtain ⟨v, _, _, hc, he, _, ho⟩ := h
  have hall : ∀ u, s.ontic.ExistsAt u c := by
    intro u
    by_cases hu : s.ontic.ExistsAt u c
    · exact hu
    · exact False.elim (ho c hc ⟨he, ⟨u, frame v u, hu⟩⟩ rfl)
  exact ⟨hc, hall w, fun u _ => hall u⟩

/-- Same-case connection into the existing Scenario conclusion. A10's
expectation selects a best interpretation reporting a cause of `x`; the
same-case bridge realizes exactly that interpretation's cause `src i x`; under
`UniversalFrame` that same bearer is an actual necessary concretum. The A10
guards do work: the conclusion is about the selected interpretation's cause of
this case. Dictionary adequacy, prior-partial-cause-to-totality transport and
objective realization remain OPEN premises carried by `src` and `bridge`. -/
theorem sameCaseNecessarySource (p : Profile I E X) (x : X)
    (s : PossibleCauseOfContingency.Scenario W B) (w : W) (src : I → X → B)
    (h : Expect p x) (bridge : SameCaseBridge p s w src x)
    (frame : PossibleCauseOfContingency.UniversalFrame s) :
    ∃ i, Best p i ∧ p.hasCause i x ∧ s.concrete (src i x) ∧
      s.ontic.ExistsAt w (src i x) ∧
      TruthCore.German.Kant.CosmologicalInference.NecessaryAt
        s.ontic w (src i x) := by
  obtain ⟨i, hi, hc⟩ := supportedInterpretation p x h
  exact ⟨i, hi, hc, totalityCauseViaNecessary s w _ frame (bridge i hi hc)⟩

/-- Projection to the exact existing Scenario conclusion. -/
theorem sameCaseScenario (p : Profile I E X) (x : X)
    (s : PossibleCauseOfContingency.Scenario W B) (w : W) (src : I → X → B)
    (h : Expect p x) (bridge : SameCaseBridge p s w src x)
    (frame : PossibleCauseOfContingency.UniversalFrame s) :
    PossibleCauseOfContingency.NecessaryConcreteAt s w := by
  obtain ⟨i, _, _, hc, he, hn⟩ := sameCaseNecessarySource p x s w src h bridge frame
  exact ⟨src i x, hc, he, hn⟩

/-- Nonvacuity: the full same-case bundle holds in the existing mixed Scenario
with the dictionary naming its necessary bearer `none`. -/
theorem sameCaseBundleNonvacuous : Expect (fixture false) false ∧
    SameCaseBridge (fixture false) PossibleCauseOfContingency.mixed false
      (fun _ _ => none) false ∧
    PossibleCauseOfContingency.UniversalFrame PossibleCauseOfContingency.mixed := by
  refine ⟨fixtureExpected, ?_, PossibleCauseOfContingency.mixedUniversal⟩
  intro _ _ _
  refine ⟨false, True.intro, ?_, True.intro, True.intro, ⟨rfl, rfl⟩, ?_⟩
  · exact ⟨True.intro, ⟨some false, True.intro,
      PossibleCauseOfContingency.mixedContingentAtFalse⟩⟩
  · intro y _ hCont hEq
    subst hEq
    rcases hCont with ⟨_, _, _, hAbsent⟩
    exact hAbsent True.intro

/-- Dictionary omission countermodel: in mixed, with the dictionary naming the
contingent bearer `some false`, full A10 expectation, UniversalFrame and the
OLD unindexed bridge all hold, yet the same-case bridge fails and the selected
interpretation's named cause is not necessary. The old composition therefore
cannot certify anything about the selected case's cause. -/
theorem dictionaryLoadBearing :
    Expect (fixture false) false ∧
    PossibleCauseOfContingency.UniversalFrame PossibleCauseOfContingency.mixed ∧
    (∀ i, Best (fixture false) i → (fixture false).hasCause i false →
      PossibleCauseOfContingency.PossiblyExternallyCausedAt
        PossibleCauseOfContingency.mixed false) ∧
    ¬ SameCaseBridge (fixture false) PossibleCauseOfContingency.mixed false
      (fun _ _ => some false) false ∧
    ¬ ∃ i, Best (fixture false) i ∧ (fixture false).hasCause i false ∧
      TruthCore.German.Kant.CosmologicalInference.NecessaryAt
        PossibleCauseOfContingency.mixed.ontic false (some false) := by
  refine ⟨fixtureExpected, PossibleCauseOfContingency.mixedUniversal,
    fun _ _ _ => PossibleCauseOfContingency.mixedPossibleExternalCause, ?_, ?_⟩
  · intro hb
    have hbest : Best (fixture false) false := by
      simp [Best, Admissible, fixture]
    obtain ⟨v, _, _, _, _, hcause, _⟩ := hb false hbest rfl
    exact absurd hcause.2 (by simp)
  · rintro ⟨_, _, _, hn⟩
    exact absurd (hn true True.intro) (by simp [PossibleCauseOfContingency.mixed])

/-- Expectation omission countermodel: with cyclic preference (no best
interpretation) the same-case bridge holds vacuously in the brute-only
Scenario for any dictionary, UniversalFrame holds, yet no necessary concretum
exists. The A10 expectation premise is load-bearing. -/
theorem expectationLoadBearing :
    SameCaseBridge { fixture false with
        preferred := fun _ _ => True, hasCause := fun _ _ => True }
      PossibleCauseOfContingency.bruteOnly false (fun _ _ => false) false ∧
    PossibleCauseOfContingency.UniversalFrame PossibleCauseOfContingency.bruteOnly ∧
    ¬ PossibleCauseOfContingency.NecessaryConcreteAt
      PossibleCauseOfContingency.bruteOnly false := by
  refine ⟨?_, PossibleCauseOfContingency.bruteOnlyUniversal,
    PossibleCauseOfContingency.bruteOnlyNoNecessary⟩
  intro i hi _
  exact False.elim (hi.2 i hi.1 trivial)

end TruthCore.Causality.A10PreferentialExpectation
