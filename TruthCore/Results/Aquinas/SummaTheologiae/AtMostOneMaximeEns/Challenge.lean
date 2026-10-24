import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (AtMostOneMaximeEns)

/-- There is at most one maximum in being. From the *quarta via*'s genus principle
(what is maximally such in a genus causes all others of that genus), Aristotle's
*Metaphysics* II.1 (a cause of a quality in another is more such than it), and
excluded middle. If `m'` were other than `m`, then `m`, being maximal in being,
would cause the being of `m'` (genus principle at *esse*; `m'` has being); a cause
of another's being is more a being than it (*Metaphysics* II.1); but nothing is
more a being than `m'`, which is also maximal. So `m'` is not other than `m`, and
by excluded middle `m = m'`. No ordering property of `MoreIn` (antisymmetry,
totality) is used: the causal premises exclude a tie. -/
theorem atMostOneMaximeEns {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    AtMostOneMaximeEns InAct MoreIn esse := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns
