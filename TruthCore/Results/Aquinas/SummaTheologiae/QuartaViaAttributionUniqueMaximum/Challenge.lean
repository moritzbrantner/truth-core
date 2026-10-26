import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionUniqueMaximum
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (AtMostOneMaximeEns)

/-- On the reading by attribution, there is at most one maximum in being. If
one thing is more a being than another exactly as it approaches a primary more
nearly (q.3 a.5 ad 2), and nothing else reaches the primary (strict primacy,
an open premise), every maximum in being is the primary, so any two are the
same. Neither the genus principle nor
*Metaphysics* II.1 is used, unlike `AtMostOneMaximeEns.atMostOneMaximeEns`. -/
theorem attributionOrderUniqueMaximum {Being Respect Degree : Type}
    [Preorder Degree]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (near : Being → Degree) (p : Being)
    (hApproach : ApproachToPrimaryReading InAct MoreIn esse near p)
    (hStrict : StrictPrimacyReading near p)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    AtMostOneMaximeEns InAct MoreIn esse := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionUniqueMaximum
