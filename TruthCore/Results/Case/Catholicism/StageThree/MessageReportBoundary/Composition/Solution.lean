module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary
public import TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary.Rival.Solution
public import TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary.Rejection.Solution

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem messageOnlyRejectsHistoricalBundle (σ : Signature) (A : Agency σ) (E : Commissioning)
    (hRival : MandateCoversOnlyMessage σ A)
    (hLink : GoverningEventInstitutionLink σ A E)
    (hActual : ActualMandatedCatholicFounding σ A) : HistoricalCommissionBundleRejected E := by
  exact noGoverningRejectsHistoricalBundle E
    (messageOnlyRejectsGoverning σ A E hRival hLink hActual)

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
