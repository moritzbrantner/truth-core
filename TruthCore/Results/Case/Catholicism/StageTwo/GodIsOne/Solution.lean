import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.Solution
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

/-- God is one (ST I q.11; *Dei Filius* ch. 1, *unum*). Whatever is God is maximal in
being, and there is at most one maximum in being
(`AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS`). -/
theorem godIsOne {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    GodIsOne IsGod := by
  -- INF-STAGE2-AT-MOST-ONE-MAXIMUM (result AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS)
  have hUnique : AtMostOneMaximeEns InAct MoreIn esse :=
    TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.atMostOneMaximeEns InAct MoreIn CausesIn esse hGenus hCauseMore hEM
  -- INF-STAGE2-GOD-IS-ONE
  intro g hg g' hg'
  exact hUnique g' g (hMaximal g' hg') (hMaximal g hg)

end TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne
