import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question105.Article5
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsMaximeEns IsFirstUnmovedMover
  MaximeEnsIsGod)

/-- The identification of the *prima via*'s mover with the *quarta via*'s
maximal being. Let `f` be a first mover moved by none and `m` maximal in being.
If `f` were other than `m`: `f` moves, so it is in act (ST I q.2 a.3), so it has
being (q.4 a.1 ad 3), so `m` causes its being (q.2 a.3, genus principle at
*esse*). `m` is God (open premise `MaximeEnsIsGod`), and every agent whose being
God causes is moved to act (q.105 a.5); but `f` is moved by none. So `f` is not
other than `m`, and by excluded middle `f = m`. -/
theorem firstMoverIsMaximeEns {Being : Type} {Respect : Type}
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
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    FirstUnmovedMoverIsMaximeEns MovedIn MovesIn InAct MoreIn esse := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns
