import Mathlib.Order.RelClasses
import TruthCore.Causality.NamedPotentialCauser
import TruthCore.Explanation.WellFoundedSource
import TruthCore.Logic.Configuration
namespace TruthCore.Results.Causality.CausalHarvest
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Modal.ExistenceDegrees
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource

/-- Operational adapter of the existing causal core, not a new discovery.
External causation is all-world; population and WF concern the selected world. -/
theorem localPSRCausalCore {World Being : Type} (m : Model World Being) (w : World)
    (hPop : PopulatedAt m w) (hWF : WellFoundedCausesAt m w)
    (hExternal : EveryExistentExternallyCaused m) :
    TruthCore.Logic.ConfigurationFalse := by
  exact all_external_causes_impossible m w hPop hWF hExternal

/-- The named selected source, rather than merely some witness, is underived
in the explicitly selected ordinary-causal-support profile R := m.Causes. -/
theorem selectedCauserUnderived {World Being : Type} (m : Ontic World Being)
    (w : World) (n : Being) (hRef : ActualReflexive m w)
    (hNec : NecessaryAt m w n) (hPotential : OtherDirectedPotentialCause m w n)
    (hNoContingent : NoContingentGroundOfNecessary m m.Causes w)
    (hUnionWF : WellFoundedUnionNecessarySupport m m.Causes w) :
    NamedNecessarilyUnderived m m.Causes w n := by
  refine ⟨hNec w hRef, hNec, ?_⟩
  intro v source hSource hEdge
  have hSourceNec := hNoContingent v source n hSource hNec hEdge
  have eSN : UnionNecessarySupport m m.Causes w source n :=
    ⟨hSourceNec, hNec, v, hSource, hEdge⟩
  have hOther : source ≠ n := by
    intro heq
    subst source
    exact @WellFounded.asymmetric _ _ hUnionWF n n eSN eSN
  obtain ⟨u, hu, hReturn⟩ :=
    hPotential w hRef source (hSourceNec w hRef) hOther
  have eNS : UnionNecessarySupport m m.Causes w n source :=
    ⟨hNec, hSourceNec, u, hNec u hu, hReturn⟩
  exact @WellFounded.asymmetric _ _ hUnionWF source n eSN eNS

theorem varyingNamedControl : VaryingNamedControl := by
  let m := TruthCore.Models.NecessarilyUnderived.varying
  have hNec : NecessaryAt m false false := by intro _ _; trivial
  have hPotential : OtherDirectedPotentialCause m false false := by
    intro v hv y hy hOther
    cases y with
    | false => exact False.elim (hOther rfl)
    | true => exact ⟨true, True.intro, rfl, rfl, rfl⟩
  refine ⟨TruthCore.Models.NecessarilyUnderived.varyingReflexive,
    hNec, hPotential,
    TruthCore.Models.NecessarilyUnderived.varyingNoContingentGround,
    TruthCore.Models.NecessarilyUnderived.varyingUnionWellFounded, ?_,
    True.intro, rfl, rfl, rfl⟩
  exact selectedCauserUnderived m false false
    TruthCore.Models.NecessarilyUnderived.varyingReflexive hNec hPotential
    TruthCore.Models.NecessarilyUnderived.varyingNoContingentGround
    TruthCore.Models.NecessarilyUnderived.varyingUnionWellFounded

theorem contingentPredecessorControl : ContingentPredecessorControl := by
  let m := contingentPredecessor
  have hNec : NecessaryAt m false false := by
    intro _ _
    exact Or.inl rfl
  have onlyFalse : ∀ x, NecessaryAt m false x → x = false := by
    intro x hx
    cases x with
    | false => rfl
    | true =>
      have he := hx true True.intro
      rcases he with he | ⟨he, _⟩
      · exact False.elim (Bool.noConfusion he)
      · exact False.elim (Bool.noConfusion he)
  have hUnionEmpty : ∀ source target,
      ¬ UnionNecessarySupport m m.Causes false source target := by
    rintro source target ⟨hs, ht, v, hv, he⟩
    exact he.2 ((onlyFalse source hs).trans (onlyFalse target ht).symm)
  refine ⟨True.intro, hNec, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv y hy hOther
    cases y with
    | false => exact False.elim (hOther rfl)
    | true => exact ⟨false, True.intro, rfl, by decide⟩
  · intro v source target he
    rcases he with ⟨rfl, hOther⟩
    refine ⟨?_, ?_, hOther⟩
    · cases source
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, rfl⟩
    · cases target
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, rfl⟩
  · refine ⟨fun target => Acc.intro target ?_⟩
    intro source he
    exact False.elim (hUnionEmpty source target he)
  · refine ⟨Or.inr ⟨rfl, rfl⟩, true, True.intro, ?_⟩
    rintro (he | ⟨he, _⟩) <;> exact Bool.noConfusion he
  · exact ⟨rfl, by decide⟩
  · intro hNoContingent
    have bad := hNoContingent false true false (Or.inr ⟨rfl, rfl⟩) hNec
      ⟨rfl, by decide⟩
    exact Bool.noConfusion (onlyFalse true bad)
  · intro hNamed
    exact hNamed.2.2 false true (Or.inr ⟨rfl, rfl⟩) ⟨rfl, by decide⟩
end TruthCore.Results.Causality.CausalHarvest
