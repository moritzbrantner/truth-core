import TruthCore.Causality.NecessaryConcreteUnderived
import TruthCore.Results.Causality.NecessaryRootFork.Solution
import TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.Solution

namespace TruthCore.Results.Causality.NecessaryConcreteUnderived

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Compose actual contingent dependence with the modal union route on the
concrete subtype. No necessary witness is assumed as a fresh premise. The
conclusion excludes existing concrete supporters only, at all admitted worlds.
No premise here establishes its own metaphysical applicability. -/
theorem checks {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w)
    (hRef : ActualReflexive m.ontic w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hUnion : ConcreteNecessaryUnionWF m w)
    (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  obtain ⟨b, hc, he, hn⟩ :=
    TruthCore.Results.Causality.NecessaryRootFork.necessaryConcreteOfActualGrounded
      m w hPop hWF hDep hEM
  have hNecessary : TruthCore.German.Kant.CosmologicalInference.NecessaryBeing
      (concreteOntic m) w := ⟨⟨b, hc⟩, he, hn⟩
  obtain ⟨target, ht, hn, hu⟩ :=
    TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks
      (concreteOntic m) (concreteSupport m) w hNecessary hRef hNoCont hUnion hEM
  refine ⟨target.val, target.property, ht, hn, ?_⟩
  intro v a ha he hEdge
  exact hu v ⟨a, ha⟩ he hEdge

/-- Joint consistency control with a genuinely contingent concrete dependent. -/
theorem jointWitness : JointWitness := by
  refine ⟨⟨false, trivial, Or.inl rfl⟩, ?_, ?_, trivial, ?_, ?_, ?_⟩
  · constructor
    intro b
    apply Acc.intro
    intro a ha
    have ha0 : a.val = false := ha.1
    apply Acc.intro
    intro c hc
    have hc1 : a.val = true := hc.2.1
    exact Bool.noConfusion (ha0.symm.trans hc1)
  · intro b _ he hcont
    cases b with
    | false =>
      obtain ⟨_, v, _, hv⟩ := hcont
      exact False.elim (hv (Or.inl rfl))
    | true => exact ⟨false, trivial, Or.inl rfl, rfl, rfl, rfl⟩
  · intro v a b ha hn hedge
    have ha0 : a.val = false := hedge.1
    intro u _
    exact Or.inl ha0
  · constructor
    intro b
    apply Acc.intro
    intro a hEdge
    obtain ⟨_, hn, v, _, hedge⟩ := hEdge
    have hb1 : b.val = true := hedge.2.1
    have hb0 : b.val = false := (hn true trivial).resolve_right Bool.noConfusion
    exact Bool.noConfusion (hb0.symm.trans hb1)
  · refine ⟨true, trivial, Or.inr rfl, true, trivial, ?_⟩
    intro h
    cases h with
    | inl h => exact Bool.noConfusion h
    | inr h => exact Bool.noConfusion h

end TruthCore.Results.Causality.NecessaryConcreteUnderived
