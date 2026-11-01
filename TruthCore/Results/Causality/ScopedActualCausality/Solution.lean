import TruthCore.Causality.ScopedActualCausality
import TruthCore.Results.Causality.AtomisticCausalSource.Solution
import TruthCore.Results.Causality.WorldSourceRegress.Solution

namespace TruthCore.Results.Causality.ScopedActualCausality
open TruthCore.Causality.ScopedActualCausality
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.WorldSourceRegress
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- A genuine pointwise generalization of the old global-policy consumer.
The SAME actual uncaused candidate is necessary in the supplied frame. -/
theorem selectedSourceNecessary {W B : Type} (m : Ontic W B) (w : W) (c : B)
    (hEM : ExcludedMiddle) (hCoverage : SelectedActualCausalCoverage m w)
    (hExists : m.ExistsAt w c)
    (hSource : ¬ ∃ y, m.ExistsAt w y ∧ m.Causes w y c) : NecessaryAt m w c := by
  intro v hwv
  rcases hEM (m.ExistsAt v c) with he | ha
  · exact he
  · obtain ⟨y, hy, hyc⟩ := hCoverage c ⟨hExists, v, hwv, ha⟩
    exact (hSource ⟨y, hy, hyc⟩).elim


/-- Structural projection; no independent causal premise is established. -/
theorem globalToSelected {W B : Type} (m : Ontic W B) (w : W)
    (hGlobal : LocalCausalPrinciple m) : SelectedActualCausalCoverage m w := by
  intro x hx
  obtain ⟨y, hy, hyx, _⟩ := hGlobal w x hx
  exact ⟨y, hy, hyx⟩

/-- Same NecessaryBeing conclusion and same four structural inputs plus EM;
only global causal coverage is replaced by selected-world coverage. -/
theorem necessaryBeing {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)]
    (hPop : ObjectPopulation (Actual m w))
    (hAtomic : AtomicParts (Actual m w))
    (hCover : ConditionalCausedSimpleCover (actualGraph m w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph m w))
    (hEM : ExcludedMiddle) (hCoverage : SelectedActualCausalCoverage m w) :
    NecessaryBeing m w := by
  obtain ⟨c, hc⟩ := TruthCore.Results.Causality.AtomisticCausalSource.source
    (actualGraph m w) hPop hAtomic hCover hNoOverlap hEM
  have hs := (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff m w c).mp hc
  exact ⟨c.val, c.property, selectedSourceNecessary m w c.val hEM hCoverage c.property hs⟩

/-- Exact existing finite ontology: structural background plus nonvacuous
selected coverage, while the old global coverage fails. -/
theorem strictControl : StrictControl := by
  let m := TruthCore.Causality.PossibleCauseOfContingency.mixed.ontic
  letI : PartialOrder (Actual m false) := MixedControl.order
  letI : LE (Actual m false) := MixedControl.order.toLE
  let effect : Actual m false := ⟨some false, rfl⟩
  have hLeEq : ∀ x y : Actual m false, x ≤ y → x = y := by
    intro x y hxy
    exact MixedControl.toOld_injective hxy
  have hSimple : ∀ x : Actual m false, IsMin x := by
    intro x y hy
    have hEq := hLeEq y x hy
    subst y
    exact le_refl x
  have hCoverage : SelectedActualCausalCoverage m false := by
    intro x hx
    refine ⟨none, True.intro, ?_⟩
    have he : x = some false := by
      cases x with
      | none =>
        rcases hx.2 with ⟨v, _, ha⟩
        exact (ha True.intro).elim
      | some b =>
        have hb : false = b := hx.1
        exact congrArg some hb.symm
    exact ⟨rfl, rfl, he⟩
  refine ⟨⟨effect⟩, ?_, ?_, ?_, hCoverage,
    TruthCore.Causality.PossibleCauseOfContingency.mixedContingentAtFalse, ?_⟩
  · intro x
    exact ⟨x, le_refl x, hSimple x⟩
  · intro _
    refine ⟨effect, ?_⟩
    rintro x ⟨_, c, hc⟩
    have he : x.val = some false := hc.2.2
    have heq : x = effect := Subtype.ext he
    exact heq ▸ le_refl effect
  · intro c e hce ⟨p, hpc, hpe⟩
    have hEq : c = e := (hLeEq p c hpc).symm.trans (hLeEq p e hpe)
    have ho : c.val = none := hce.2.1
    have he : e.val = some false := hce.2.2
    have hv := congrArg Subtype.val hEq
    rw [ho, he] at hv
    cases hv
  · intro hg
    obtain ⟨c, _, hc, _⟩ := hg true (some true)
      TruthCore.Causality.PossibleCauseOfContingency.mixedContingentAtTrue
    exact TruthCore.Causality.PossibleCauseOfContingency.mixedHasContingentUncausedRoot.2 c hc

end TruthCore.Results.Causality.ScopedActualCausality
