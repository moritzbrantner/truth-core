module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem actualMessageOnlyRejectsCatholicScope (σ : Signature) (A : Agency σ)
    (hRival : MandateCoversOnlyMessage σ A)
    (hActual : ActualMandatedCatholicFounding σ A) : CatholicMandateScopeRejected σ A := by
  obtain ⟨g, hm, hf, hv⟩ := hActual
  intro hs
  exact messageRival_excludes_scope σ A g hm hf hv ⟨hs, hRival⟩

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
