import TruthCore.Case.Catholicism.StageOneQuintaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.Government
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaDirectingIsMoving
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (DirectingIsMoving)
theorem directingIsMoving {Being : Type} {Respect : Type} {End : Type}
    (MovesIn : Being → Being → Respect → Prop)
    (Directs : Being → Being → End → Prop) (Governs : Being → Being → Prop)
    (hGovern : DirectingToAnEndIsGoverningReading Directs Governs)
    (hChange : GovernmentEffectsChangeReading MovesIn Governs) :
    DirectingIsMoving MovesIn Directs := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaDirectingIsMoving
