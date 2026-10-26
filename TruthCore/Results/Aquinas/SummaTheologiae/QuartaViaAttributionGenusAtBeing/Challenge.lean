import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionGenusAtBeing
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- On the reading by attribution, the genus principle holds at being. If one
thing is more a being than another exactly as it approaches a primary more
nearly (q.3 a.5 ad 2), and nothing else reaches the primary (strict primacy, an
open premise), then whatever is maximal in being is the primary; if every
creature is ordered to the primary as to its cause (q.13 a.5) and everything
other than the primary is a creature (an open premise), the maximum causes the
being of every other being. Only the instance at being is derived: the genus
principle for other perfections is not touched. -/
theorem attributionOrderGenusPrincipleAtBeing {Being Respect Degree : Type}
    [Preorder Degree]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (Creature : Being → Prop)
    (esse : Respect) (near : Being → Degree) (p : Being)
    (hApproach : ApproachToPrimaryReading InAct MoreIn esse near p)
    (hStrict : StrictPrimacyReading near p)
    (hOrdered : OrderedToPrimaryAsCauseReading InAct CausesIn Creature esse p)
    (hCreatures : OthersAreCreaturesReading Creature p)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionGenusAtBeing
