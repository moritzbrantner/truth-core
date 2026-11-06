module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem historicalBundleGivesGoverning (E : Commissioning)
    (h : CommissionReportsGoBackToJesus E) : GoverningGrantExists E := by
  exact (commission_reports_give_teach_and_governing E h).2

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
