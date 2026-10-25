import TruthCore.Case.Catholicism.StageOneQuintaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.Government
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaDirectingIsMoving
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (DirectingIsMoving)

/-- The *quinta via*'s bridge that directing is moving, from ST I q.103: to
direct a thing to its end is to govern it (a.3), and government is a change the
governor effects in what it governs (a.5 ad 2). -/
theorem directingIsMoving {Being : Type} {Respect : Type} {End : Type}
    (MovesIn : Being → Being → Respect → Prop)
    (Directs : Being → Being → End → Prop) (Governs : Being → Being → Prop)
    (hGovern : DirectingToAnEndIsGoverningReading Directs Governs)
    (hChange : GovernmentEffectsChangeReading MovesIn Governs) :
    DirectingIsMoving MovesIn Directs := by
  intro d x e hDirects
  -- INF-AQUINAS-Q103-DIRECTING-IS-GOVERNING
  have hGoverns : Governs d x := hGovern d x e hDirects
  -- INF-AQUINAS-Q103-GOVERNING-IS-MOVING
  exact hChange d x hGoverns

end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaDirectingIsMoving
