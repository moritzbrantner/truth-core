import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
import TruthCore.Greek.Aristotle.Metaphysics
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

theorem godIsSimple {Being : Type} {Respect : Type}
    (IsGod Composite : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) :
    GodIsSimple IsGod Composite := by
  -- INF-STAGE2-GOD-IS-SIMPLE: a composite has a uniting cause of its being (q.3 a.7),
  -- which would be more a being than it (Metaphysics II.1); but God is maximal in being
  intro g hg hComposite
  obtain ⟨c, hOther, hCauses⟩ := hUniting g hComposite
  exact (hMaximal g hg).2 c (hCauseMore c g esse hOther hCauses)

end TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple
