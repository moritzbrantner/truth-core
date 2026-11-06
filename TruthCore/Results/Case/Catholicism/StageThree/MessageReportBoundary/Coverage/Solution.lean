module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem institutionalTransferCoverage (σ : Signature) (A : Agency σ) (E : Commissioning)
    (hEM : TruthCore.Logic.ExcludedMiddle) : InstitutionalTransferCases σ A E := by
  cases hEM (InstitutionalTransferCountercase σ A E) with
  | inl h => exact Or.inr h
  | inr h =>
    apply Or.inl
    intro g hm hf hv hg
    cases hEM (A.FoundedInMandate σ.jesus g σ.catholicChurch) with
    | inl hi => exact hi
    | inr hi => exact False.elim (h ⟨g, hm, hf, hv, hg, hi⟩)

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
