import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question105.Article5
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsMaximeEns IsFirstUnmovedMover
  MaximeEnsIsGod)

/-- Separate sufficient equality-decision interface. All nonlogical premises remain open.
No existence follows from naming or identifying supplied witnesses. No necessity,
minimality, strict-strength or philosophical-discharge claim. The historical
end, where present, retains the existing structural transcription. -/
theorem firstMoverIsMaximeEns {Being : Type} {Respect : Type}
    [DecidableEq Being]
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (God : Being → Prop)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hGod : MaximeEnsIsGod InAct MoreIn esse God)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God) :
    FirstUnmovedMoverIsMaximeEns MovedIn MovesIn InAct MoreIn esse := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity
