import TruthCore.Bridges.PerSeRegressFiniteGrounding
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Bridges.PerSeRegressFiniteGrounding
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality
open TruthCore.Bridges
/-- Bridge (#401): the secunda via's no-regress premise
(`STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES`: the per se link
`CausesAsCaused` is well-founded), with excluded middle (`STMT-EXCLUDED-MIDDLE`)
and the finite-grounding theorem of `TruthCore.Causality.EssentialPower`
(`STMT-FINITE-GROUNDING-HAS-SOURCE`), yields that every being reaches by a finite
per se path a being with no per se cause upstream
(`STMT-EVERY-BEING-HAS-FINITE-PER-SE-PATH-TO-UNCAUSED`).

By well-founded induction every being is finitely grounded in the inductive
sense, with "intrinsic" read as "has no per se cause": excluded middle splits on
whether it has an upstream per se cause; if so it borrows from that cause, which
is grounded by the induction hypothesis. The finite-grounding theorem then gives
the finite path. Only the path structure of `FinitelyGroundedPower` is used, not
a power semantics (`DISAMB-CAUSAL-POWER-GROUNDING`). -/
theorem everyBeingHasFinitePerSePathToUncausedOfNoRegress {Being : Type} (CausesAsCaused : Being → Being → Prop)
    (hNoRegress : NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused)
    (hExcludedMiddle : TruthCore.Logic.ExcludedMiddle)
    (hFiniteGrounding : FiniteGroundingHasSource) :
    EveryBeingHasFinitePerSePathToUncaused CausesAsCaused := by
  intro x
  have hGrounded : FinitelyGroundedPower CausesAsCaused
      (fun source => ¬ ∃ y, CausesAsCaused y source) x := by
    induction hNoRegress x with
    | intro x _ ih =>
      cases hExcludedMiddle (∃ y, CausesAsCaused y x) with
      | inl hCaused =>
        -- x has an upstream per se cause, grounded by the induction hypothesis.
        obtain ⟨y, hy⟩ := hCaused
        exact FinitelyGroundedPower.borrowed hy (ih y hy)
      | inr hUncaused =>
        -- x has no upstream per se cause: it is its own source.
        exact FinitelyGroundedPower.intrinsic x hUncaused
  exact hFiniteGrounding Being CausesAsCaused _ x hGrounded
end TruthCore.Results.Bridges.PerSeRegressFiniteGrounding
