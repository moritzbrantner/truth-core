module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem messageOnlyRejectsGoverning (σ : Signature) (A : Agency σ) (E : Commissioning)
    (hRival : MandateCoversOnlyMessage σ A)
    (hLink : GoverningEventInstitutionLink σ A E)
    (hActual : ActualMandatedCatholicFounding σ A) : NoGoverningGrant E := by
  sorry

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
