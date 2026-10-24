import TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question13.Article8
namespace TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGod
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (AtMostOneMaximeEns MaximeEnsIsGod)

/-- Whatever is maximal in being is God. Let `m` be maximal in being. By the genus
principle at *esse*, `m` causes the being of every other being. By the uniqueness
result (`AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS`), every being maximal in being
is `m`. So `m` is the only being that is above all and the principle of all, and
by the nominal definition of the name (q.13 a.8 ad 2, *et hoc dicimus Deum*),
`m` is God. -/
theorem maximeEnsIsGod {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hName : GodNamesTheUniqueMaximeEnsReading InAct MoreIn CausesIn esse God) :
    MaximeEnsIsGod InAct MoreIn esse God := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGod
