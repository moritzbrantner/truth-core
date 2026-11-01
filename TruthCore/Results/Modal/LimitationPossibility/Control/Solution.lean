import TruthCore.Results.Modal.LimitationPossibility.Solution
namespace TruthCore.Results.Modal.LimitationPossibility.Control
open TruthCore.Modal.LimitationPossibility
open TruthCore.Isabelle.AFP.GoedelGod
open TruthCore.Logic (ExcludedMiddle)
/-- One joint formal fixture under explicit EM, not deficiency truth or a
metaphysically possible God/necessary-being interpretation. -/
theorem control (hEM : ExcludedMiddle) : JointControl := by
  have hKnown : KnownLimitingAt controlLimitation controlKnown () := by
    rintro ⟨_, hFalse⟩
    exact hFalse
  have hTarget : NonlimitingAt controlLimitation controlTarget () := by
    intro hNone
    exact hNone ⟨true, rfl⟩
  have hClosure : BackwardClosedAt controlFrame controlLimitation () := by
    intro Phi Psi hInclusion hNone hSome
    obtain ⟨x, hx⟩ := hSome
    exact hNone ⟨x, hInclusion () trivial x hx⟩
  have hNegTarget : NonlimitingAt controlLimitation
      (fun x w => ¬ controlTarget x w) () := by
    intro hNone
    exact hNone ⟨false, fun h => Bool.noConfusion h⟩
  have hPossible := TruthCore.Results.Modal.LimitationPossibility.possible
    controlFrame controlLimitation controlKnown controlTarget ()
    hKnown hTarget hClosure hEM
  have hNegPossible : PossiblyExemplifiedAt controlFrame
      (fun x w => ¬ controlTarget x w) () := by
    exact ⟨(), trivial, false, fun h => Bool.noConfusion h⟩
  refine ⟨hKnown, hTarget, hClosure, hNegTarget, hPossible, hNegPossible, ?_⟩
  intro hScott
  exact hScott () controlTarget hNegTarget hTarget
end TruthCore.Results.Modal.LimitationPossibility.Control
