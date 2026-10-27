import TruthCore.Case.Catholicism.StageThree.Commissions

namespace TruthCore.Results.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions

/-- The narrow scope premise `STMT-MANDATE-COVERS-JESUS-FOUNDING-OF-CATHOLIC-CHURCH`
follows from the report-to-event premise for the reported commissions and the
premise that the Catholic Church, if Jesus founded it, was founded in the
apostles he commissioned: if Matthew 28.18-20 and at least one of the four
governing commissions go back to Jesus, then, whenever Jesus holds a mandate
from `g` and founded the Catholic Church as a visible society with authority,
he founded it in that mandate and commissioned it to teach. -/
theorem narrow_scope_from_commissions (σ : Signature) (A : Agency σ)
    (E : Commissioning)
    (hReports : CommissionReportsGoBackToJesus E)
    (hLink : ChurchFoundedInCommissionedApostles σ A E) :
    MandatedFoundingOfCatholicChurch σ A := by
  intro g hMandate hFounded hVisible
  -- Premise 1: Jesus gave the power to teach and some governing power.
  obtain ⟨hTeach, p, hGoverning, hGave⟩ := commission_reports_give_teach_and_governing E hReports
  -- Premise 2 at g: the governing power makes the founding one in the mandate,
  -- and the power to teach is a commission of the Church to teach.
  have hL := hLink g hMandate hFounded hVisible
  exact ⟨hL.1 p hGoverning hGave, hL.2 hTeach⟩

end TruthCore.Results.Case.Catholicism.StageThree.Commissions
