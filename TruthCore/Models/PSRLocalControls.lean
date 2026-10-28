import TruthCore.Models.PSR
import TruthCore.Modal.WorldwiseExplanation
import TruthCore.Explanation.WellFoundedSource
import TruthCore.Explanation.NoBruteExistence

/-! Local explanation-coverage evaluations on unchanged registered PSR data.
Reasons remain stipulated tokens; neither causal nor grounding explanation is
identified with `explains`. The empty control has an inhabited candidate domain
but no actual individuals. No metaphysical adequacy or ontology label follows. -/
namespace TruthCore.Models.PSRLocalControls
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.NoBruteExistence
open TruthCore.Explanation.WellFoundedSource

private theorem excludesBrute {m : Model W E} {w : W}
    (h : NoBruteExistenceAt m w) : ¬ BruteExistenceAt m w := by
  rintro ⟨x, hx, hn⟩
  exact hn (h x hx)

private theorem excludesNoBrute {m : Model W E} {w : W}
    (h : BruteExistenceAt m w) : ¬ NoBruteExistenceAt m w := by
  intro hn
  exact excludesBrute hn h

theorem intrinsicNoBrute : NoBruteExistenceAt PSR.Intrinsic.model false :=
  PSR.Intrinsic.evaluation1 false

theorem intrinsicNotBrute : ¬ BruteExistenceAt PSR.Intrinsic.model false :=
  excludesBrute intrinsicNoBrute

theorem contingentBrute : BruteExistenceAt PSR.ContingentOnly.model false := by
  refine ⟨false, Or.inl rfl, ?_⟩
  rintro ⟨_, h⟩
  exact Bool.noConfusion h.2.1

theorem contingentNotNoBrute : ¬ NoBruteExistenceAt PSR.ContingentOnly.model false :=
  excludesNoBrute contingentBrute

theorem contingentPopulated : PopulatedAt PSR.ContingentOnly.model false :=
  ⟨false, Or.inl rfl⟩

theorem contingentWellFounded : WellFoundedCausesAt PSR.ContingentOnly.model false := by
  refine ⟨fun x => Acc.intro x ?_⟩
  intro _ h
  exact h.elim

theorem contingentNotExternal : ¬ EveryExistentExternallyCaused PSR.ContingentOnly.model := by
  intro h
  obtain ⟨_, _, _, hc⟩ := h false false (Or.inl rfl)
  exact hc.elim

theorem mutualNoBrute : NoBruteExistenceAt mutualCauses () := mutualCausesPSR ()

theorem mutualNotBrute : ¬ BruteExistenceAt mutualCauses () :=
  excludesBrute mutualNoBrute

theorem emptyNoBrute : NoBruteExistenceAt emptyWorld () := emptyWorldPSR ()

theorem emptyNotBrute : ¬ BruteExistenceAt emptyWorld () :=
  excludesBrute emptyNoBrute

theorem alternatingNoBrute : NoBruteExistenceAt TruthCore.Modal.WorldwiseExplanation.alternating false :=
  TruthCore.Modal.WorldwiseExplanation.alternatingPSR false

theorem alternatingNotBrute : ¬ BruteExistenceAt TruthCore.Modal.WorldwiseExplanation.alternating false :=
  excludesBrute alternatingNoBrute

theorem alternatingPopulated : PopulatedAt TruthCore.Modal.WorldwiseExplanation.alternating false :=
  ⟨false, rfl⟩

theorem alternatingWellFounded : WellFoundedCausesAt TruthCore.Modal.WorldwiseExplanation.alternating false := by
  refine ⟨fun x => Acc.intro x ?_⟩
  intro _ h
  exact h.elim

theorem alternatingNotExternal : ¬ EveryExistentExternallyCaused TruthCore.Modal.WorldwiseExplanation.alternating := by
  intro h
  obtain ⟨_, _, _, hc⟩ := h false false rfl
  exact hc.elim

/-- A brute fact about one individual does not preclude a different explained
existent without an incoming existing cause in the same world. -/
theorem contingentExplainedSource : ExplainedSourceAt PSR.ContingentOnly.model false := by
  refine ⟨true, .circumstance true, Or.inr ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨_, _, hc⟩
  exact hc.elim

theorem alternatingExplainedSource : ExplainedSourceAt TruthCore.Modal.WorldwiseExplanation.alternating false := by
  refine ⟨false, .circumstance false, rfl, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨_, _, hc⟩
  exact hc.elim

theorem emptyNoExplainedSource : ¬ ExplainedSourceAt emptyWorld () := by
  rintro ⟨_, _, hx, _, _⟩
  exact hx.elim

end TruthCore.Models.PSRLocalControls
