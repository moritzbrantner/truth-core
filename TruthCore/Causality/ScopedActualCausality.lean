import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Causality.WorldSourceRegress
import TruthCore.Causality.PossibleCauseOfContingency
import TruthCore.Logic.ExcludedMiddle
import Mathlib.Order.Basic

/-! Analyst restriction of ordinary causal coverage to ONE selected world.
The complete-production interpretation is OPEN, not inferred from grounding or
from the source's nonmodal argument. No distinctness, concreteness, endpoint
policy or frame property is built into the predicate. -/
namespace TruthCore.Causality.ScopedActualCausality
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Logic (ExcludedMiddle)

/-- Every actually contingent individual at this world has an existing cause
there. ContingentAt already includes existence of the target at that world. -/
def SelectedActualCausalCoverage {W B : Type} (m : Ontic W B) (w : W) : Prop :=
  ∀ x, ContingentAt m w x → ∃ y, m.ExistsAt w y ∧ m.Causes w y x


namespace MixedControl
open TruthCore.Causality.PossibleCauseOfContingency (mixed)

/-- Map the existing selected actual nodes to the old two-atom fixture. The
absent some true is excluded by subtype membership, not deleted from Ontic. -/
def toOld (x : Actual mixed.ontic false) : Fixture.Object :=
  match x.val with
  | none => .origin
  | some _ => .effect

theorem toOld_injective : Function.Injective toOld := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply Subtype.ext
  cases x <;> cases y <;> simp_all [toOld]
  change false = _ at hx hy
  exact hx.symm.trans hy

/-- Transport the EXISTING identity-parthood order with Mathlib. The ordinary
Option/Bool linear order would identify unequal objects as parts and violate
nonoverlap, so it is not the intended fixture order. No Ontic field changes. -/
@[instance_reducible] def order : PartialOrder (Actual mixed.ontic false) :=
  PartialOrder.lift toOld toOld_injective

end MixedControl

/-- All four nonlogical structural inputs and selected-world coverage hold
on the exact old mixed ontology, with a genuinely contingent caused target.
Global coverage fails in the other world. No EM premise is part of this model
certificate; no real/metaphysical possibility or causal adequacy is asserted. -/
def StrictControl : Prop :=
  letI := MixedControl.order
  let m := TruthCore.Causality.PossibleCauseOfContingency.mixed.ontic
  ObjectPopulation (Actual m false) ∧ AtomicParts (Actual m false) ∧
  ConditionalCausedSimpleCover (actualGraph m false) ∧
  CauseEffectNonoverlap (actualGraph m false) ∧
  SelectedActualCausalCoverage m false ∧ ContingentAt m false (some false) ∧
  ¬ LocalCausalPrinciple m

end TruthCore.Causality.ScopedActualCausality
